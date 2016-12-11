{-# LANGUAGE ExplicitForAll      #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Compilation, execution and introspection of queries
module Database.DSH.Compiler
    ( -- * Compiling and executing queries
      runQ
    , compileOptQ
      -- * Debugging and benchmarking queries
    , codeQ
    , vectorPlanQ
    , showComprehensionsQ
    , showComprehensionsLogQ
    , showComprehensionsOptQ
    , showDesugaredQ
    , showDesugaredOptQ
    , showLiftedQ
    , showLiftedOptQ
    , showFlattenedQ
    , showFlattenedOptQ
    , showVectorizedQ
    , showVectorizedOptQ
    , showDelayedQ
    , showDelayedOptQ
    , showBackendCodeQ
      -- * Comprehension optimizers
    , module Database.DSH.CL.Opt
      -- * Vectorization
    , module Database.DSH.Translate.Vectorize
    ) where

import           Control.Arrow
import           Control.Monad
import qualified Data.Foldable                      as F
import qualified Data.IntMap                        as IM
import           System.Process
import           System.Random
import           Text.Printf

import           Database.DSH.Translate.Frontend2CL

import           Database.DSH.Backend
import qualified Database.DSH.CL.Lang               as CL
import           Database.DSH.CL.Opt
import           Database.DSH.Common.Pretty
import           Database.DSH.Common.QueryPlan
import           Database.DSH.Common.Vector
import           Database.DSH.Common.VectorLang
import           Database.DSH.Execute
import           Database.DSH.FKL.Rewrite
import           Database.DSH.Frontend.Internals
import           Database.DSH.NKL.Rewrite
import           Database.DSH.SL
import           Database.DSH.SL.Typing
import           Database.DSH.Translate.CL2NKL
import           Database.DSH.Translate.NKL2FKL
import           Database.DSH.Translate.Vectorize
import           Database.DSH.VSL

--------------------------------------------------------------------------------

-- | The frontend- and backend-independent part of the compiler.
compileQ :: VectorLang v => CLOptimizer -> CL.Expr -> QueryPlan (v TExpr TExpr) DVec
compileQ clOpt = (fst . clOpt) >>>
                 desugarComprehensions  >>>
                 optimizeNKL            >>>
                 flatTransform          >>>
                 vectorize

-- | The frontend- and backend-independent part of the compiler. Compile a
-- comprehension expression into optimized vector plans.
compileOptQ :: VectorLang v => CLOptimizer -> CL.Expr -> QueryPlan (v TExpr TExpr) DVec
compileOptQ clOpt = compileQ clOpt >>> optimizeVectorPlan

--------------------------------------------------------------------------------

runQ :: forall a b v. (VectorLang v, BackendVector b, QA a)
     => BackendCodeGen (v TExpr TExpr) b
     -> BackendConn b
     -> Q a
     -> IO a
runQ codeGen conn (Q q) = do
    let ty = reify (undefined :: Rep a)
    let comprehensions = toComprehensions q
    let vectorPlan = compileOptQ optBU comprehensions
    let backendCode = codeGen vectorPlan
    frExp <$> execQueryBundle conn backendCode ty

--------------------------------------------------------------------------------

-- | Compile a query to a vector plan
vectorPlanQ :: VectorLang v => CLOptimizer -> Q a -> QueryPlan (v TExpr TExpr) DVec
vectorPlanQ clOpt (Q q) = compileOptQ clOpt $ toComprehensions q

-- | Compile a query to the actual backend code that will be executed
-- (for benchmarking purposes).
codeQ :: VectorLang v => CLOptimizer -> BackendCodeGen (v TExpr TExpr) b -> Q a -> [b]
codeQ clOpt codeGen (Q q) =
    let vectorPlan = compileOptQ clOpt $ toComprehensions q
        backendCode = codeGen vectorPlan
    in F.foldr (:) [] backendCode

--------------------------------------------------------------------------------

decorate :: String -> String
decorate msg = sepLine ++ msg ++ "\n" ++ sepLine
  where
    sepLine = replicate 80 '-' ++ "\n"

-- | Show comprehensions with an optional optimizer (CL)
showComprehensionsQ :: CLOptimizer -> Q a -> IO ()
showComprehensionsQ clOpt (Q q) = do
    let cl = fst $ clOpt $ toComprehensions q
    putStrLn $ decorate $ pp cl

-- | Show comprehensions with an optional optimizer and display the rewriting
-- log (CL)
showComprehensionsLogQ :: CLOptimizer -> Q a -> IO ()
showComprehensionsLogQ clOpt (Q q) = do
    let (cl, rewriteLog) = clOpt $ toComprehensions q
    putStrLn rewriteLog
    putStrLn $ decorate $ pp cl

-- | Show optimized comprehensions (CL)
showComprehensionsOptQ :: Q a -> IO ()
showComprehensionsOptQ (Q q) = do
    let cl = fst $ optBU $ toComprehensions q
    putStrLn $ decorate $ pp cl

-- | Show unoptimized desugared iterators (CL)
showDesugaredQ :: CLOptimizer -> Q a -> IO ()
showDesugaredQ clOpt (Q q) = do
    let nkl = desugarComprehensions
              $ (fst . clOpt)
              $ toComprehensions q
    putStrLn $ decorate $ pp nkl

-- | Show optimized desugared iterators (CL)
showDesugaredOptQ :: CLOptimizer -> Q a -> IO ()
showDesugaredOptQ clOpt (Q q) = do
    let nkl = optimizeNKL
              $ desugarComprehensions
              $ (fst . clOpt)
              $ toComprehensions q
    putStrLn $ decorate $ pp nkl

-- | Show unoptimized lifted operators (FKL intermediate)
showLiftedQ :: CLOptimizer -> Q a -> IO ()
showLiftedQ clOpt (Q q) = do
    let fkl = liftOperators
              $ optimizeNKL
              $ desugarComprehensions
              $ (fst . clOpt)
              $ toComprehensions q
    putStrLn $ decorate $ pp fkl

-- | Show optimized lifted operators (FKL intermediate)
showLiftedOptQ :: CLOptimizer -> Q a -> IO ()
showLiftedOptQ clOpt (Q q) = do
    let fkl = optimizeFKL
              $ liftOperators
              $ optimizeNKL
              $ desugarComprehensions
              $ (fst . clOpt)
              $ toComprehensions q
    putStrLn $ decorate $ pp fkl

-- | Show unoptimized flattened query (FKL)
showFlattenedQ :: CLOptimizer -> Q a -> IO ()
showFlattenedQ clOpt (Q q) = do
    let fkl = normalizeLifted
              $ optimizeFKL
              $ liftOperators
              $ optimizeNKL
              $ desugarComprehensions
              $ (fst . clOpt)
              $ toComprehensions q
    putStrLn $ decorate $ pp fkl

-- | Show optimized flattened query (FKL)
showFlattenedOptQ :: CLOptimizer -> Q a -> IO ()
showFlattenedOptQ clOpt (Q q) = do
    let fkl = optimizeNormFKL
              $ normalizeLifted
              $ optimizeFKL
              $ liftOperators
              $ optimizeNKL
              $ desugarComprehensions
              $ (fst . clOpt)
              $ toComprehensions q
    putStrLn $ decorate $ pp fkl

fileId :: IO String
fileId = replicateM 8 (randomRIO ('a', 'z'))

-- | Show unoptimized vector plan (SL)
showVectorizedQ :: CLOptimizer -> Q a -> IO ()
showVectorizedQ clOpt (Q q) = do
    let cl = toComprehensions q
    let vl = compileQ clOpt cl :: QueryPlan TSL DVec
    case inferSLTypes (queryDag vl) of
        Left e    -> putStrLn $ "Type inference failed for unoptimized plan\n" ++ e
        Right tys -> putStrLn $ pp $ IM.toList tys
    h <- fileId
    let fileName = "q_vl_" ++ h
    exportPlan fileName vl
    void $ runCommand $ printf "stack exec sldot -- -i %s.plan | dot -Tpdf -o %s.pdf && open %s.pdf" fileName fileName fileName

-- | Show optimized vector plan (SL)
showVectorizedOptQ :: CLOptimizer -> Q a -> IO ()
showVectorizedOptQ clOpt (Q q) = do
    let vl = compileQ clOpt $ toComprehensions q :: QueryPlan TSL DVec
    case inferSLTypes (queryDag vl) of
        Left e  -> putStrLn $ "Type inference failed for unoptimized plan\n" ++ e
        Right _ -> do
            let vlOpt = optimizeVectorPlan vl
            case inferSLTypes (queryDag vlOpt) of
                Left e    -> putStrLn $ "Type inference failed for optimized plan\n" ++ e
                Right tys -> putStrLn $ pp $ IM.toList tys
            h <- fileId
            let fileName = "q_vl_" ++ h
            exportPlan fileName vlOpt
            void $ runCommand $ printf "stack exec sldot -- -i %s.plan | dot -Tpdf -o %s.pdf && open %s.pdf" fileName fileName fileName

-- | Show unoptimized vector plan (SL)
showDelayedQ :: CLOptimizer -> Q a -> IO ()
showDelayedQ clOpt (Q q) = do
    let cl = toComprehensions q
    let vl = compileQ clOpt cl :: QueryPlan TVSL DVec
    h <- fileId
    let fileName = "q_vl_" ++ h
    exportPlan fileName vl
    void $ runCommand $ printf "stack exec vsldot -- -i %s.plan | dot -Tpdf -o %s.pdf && open %s.pdf" fileName fileName fileName

-- | Show unoptimized vector plan (SL)
showDelayedOptQ :: CLOptimizer -> Q a -> IO ()
showDelayedOptQ clOpt (Q q) = do
    let cl = toComprehensions q
    let vl = compileOptQ clOpt cl :: QueryPlan TVSL DVec
    h <- fileId
    let fileName = "q_vl_" ++ h
    exportPlan fileName vl
    void $ runCommand $ printf "stack exec vsldot -- -i %s.plan | dot -Tpdf -o %s.pdf && open %s.pdf" fileName fileName fileName

-- | Show all backend queries produced for the given query
showBackendCodeQ :: forall a b v. (VectorLang v, Show b)
                 => CLOptimizer
                 -> BackendCodeGen (v TExpr TExpr) b
                 -> Q a
                 -> IO ()
showBackendCodeQ clOpt codeGen q = do
    putStrLn sepLine
    forM_ (codeQ clOpt codeGen q) $ \code -> do
         putStrLn $ show code
         putStrLn sepLine

  where
    sepLine = replicate 80 '-'
