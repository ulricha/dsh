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
      -- * Comprehension optimizers
    , module Database.DSH.CL.Opt
      -- * Vectorization
    , module Database.DSH.Translate.Vectorize
    ) where

import           Control.Arrow
import           Control.Monad
import qualified Data.Foldable                      as F
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
import           Database.DSH.Execute
import           Database.DSH.FKL.Rewrite
import           Database.DSH.Frontend.Internals
import           Database.DSH.NKL.Rewrite
import           Database.DSH.Translate.CL2NKL
import           Database.DSH.Translate.NKL2FKL
import           Database.DSH.Translate.Vectorize
import           Database.DSH.SL
import           Database.DSH.VSL

--------------------------------------------------------------------------------

-- | The frontend- and backend-independent part of the compiler.
compileQ :: VectorLang v => CLOptimizer -> CL.Expr -> QueryPlan v DVec
compileQ clOpt = (fst . clOpt) >>>
                 desugarComprehensions  >>>
                 optimizeNKL            >>>
                 flatTransform          >>>
                 vectorize

-- | The frontend- and backend-independent part of the compiler. Compile a
-- comprehension expression into optimized vector plans.
compileOptQ :: VectorLang v => CLOptimizer -> CL.Expr -> QueryPlan v DVec
compileOptQ clOpt = compileQ clOpt >>> optimizeVectorPlan

--------------------------------------------------------------------------------

runQ :: forall a b v. (VectorLang v, BackendVector b, QA a)
     => BackendCodeGen v b
     -> BackendConn b
     -> Q a
     -> IO a
runQ codeGen conn (Q q) = do
    let ty = reify (undefined :: Rep a)
    let comprehensions = toComprehensions q
    let vectorPlan = compileOptQ optimizeComprehensions comprehensions
    let backendCode = codeGen vectorPlan
    frExp <$> execQueryBundle conn backendCode ty

--------------------------------------------------------------------------------

-- | Compile a query to a vector plan
vectorPlanQ :: (VectorLang v, QA a)
            => Q a
            -> QueryPlan v DVec
vectorPlanQ (Q q) = compileOptQ optimizeComprehensions $ toComprehensions q

-- | Compile a query to the actual backend code that will be executed
-- (for benchmarking purposes).
codeQ :: (VectorLang v, BackendVector b, QA a)
      => BackendCodeGen v b
      -> Q a
      -> [b]
codeQ codeGen (Q q) =
    let vectorPlan = compileOptQ optimizeComprehensions $ toComprehensions q
        backendCode = codeGen vectorPlan
    in F.foldr (:) [] backendCode

--------------------------------------------------------------------------------

decorate :: String -> String
decorate msg = sepLine ++ msg ++ "\n" ++ sepLine
  where
    sepLine = replicate 80 '-' ++ "\n"

-- | Show comprehensions with an optional optimizer (CL)
showComprehensionsQ :: forall a.QA a => CLOptimizer -> Q a -> IO ()
showComprehensionsQ clOpt (Q q) = do
    let cl = fst $ clOpt $ toComprehensions q
    putStrLn $ decorate $ pp cl

-- | Show comprehensions with an optional optimizer and display the rewriting
-- log (CL)
showComprehensionsLogQ :: forall a.QA a => CLOptimizer -> Q a -> IO ()
showComprehensionsLogQ clOpt (Q q) = do
    let (cl, rewriteLog) = clOpt $ toComprehensions q
    putStrLn rewriteLog
    putStrLn $ decorate $ pp cl

-- | Show optimized comprehensions (CL)
showComprehensionsOptQ :: forall a. QA a => Q a -> IO ()
showComprehensionsOptQ (Q q) = do
    let cl = fst $ optimizeComprehensions $ toComprehensions q
    putStrLn $ decorate $ pp cl

-- | Show unoptimized desugared iterators (CL)
showDesugaredQ :: forall a. QA a => CLOptimizer -> Q a -> IO ()
showDesugaredQ clOpt (Q q) = do
    let nkl = desugarComprehensions
              $ (fst . clOpt)
              $ toComprehensions q
    putStrLn $ decorate $ pp nkl

-- | Show optimized desugared iterators (CL)
showDesugaredOptQ :: forall a. QA a => CLOptimizer -> Q a -> IO ()
showDesugaredOptQ clOpt (Q q) = do
    let nkl = optimizeNKL
              $ desugarComprehensions
              $ (fst . clOpt)
              $ toComprehensions q
    putStrLn $ decorate $ pp nkl

-- | Show unoptimized lifted operators (FKL intermediate)
showLiftedQ :: forall a. QA a => CLOptimizer -> Q a -> IO ()
showLiftedQ clOpt (Q q) = do
    let fkl = liftOperators
              $ optimizeNKL
              $ desugarComprehensions
              $ (fst . clOpt)
              $ toComprehensions q
    putStrLn $ decorate $ pp fkl

-- | Show optimized lifted operators (FKL intermediate)
showLiftedOptQ :: forall a. QA a => CLOptimizer -> Q a -> IO ()
showLiftedOptQ clOpt (Q q) = do
    let fkl = optimizeFKL
              $ liftOperators
              $ optimizeNKL
              $ desugarComprehensions
              $ (fst . clOpt)
              $ toComprehensions q
    putStrLn $ decorate $ pp fkl

-- | Show unoptimized flattened query (FKL)
showFlattenedQ :: forall a. QA a => CLOptimizer -> Q a -> IO ()
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
showFlattenedOptQ :: forall a. QA a => CLOptimizer -> Q a -> IO ()
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
showVectorizedQ :: forall a. QA a => CLOptimizer -> Q a -> IO ()
showVectorizedQ clOpt (Q q) = do
    let cl = toComprehensions q
    let vl = compileQ clOpt cl :: QueryPlan SL DVec
    h <- fileId
    let fileName = "q_vl_" ++ h
    exportPlan fileName vl
    void $ runCommand $ printf "stack exec sldot -- -i %s.plan | dot -Tpdf -o %s.pdf && open %s.pdf" fileName fileName fileName

-- | Show optimized vector plan (SL)
showVectorizedOptQ :: forall a. QA a => CLOptimizer -> Q a -> IO ()
showVectorizedOptQ clOpt (Q q) = do
    let vl = compileOptQ clOpt $ toComprehensions q :: QueryPlan SL DVec
    h <- fileId
    let fileName = "q_vl_" ++ h
    exportPlan fileName vl
    void $ runCommand $ printf "stack exec sldot -- -i %s.plan | dot -Tpdf -o %s.pdf && open %s.pdf" fileName fileName fileName

-- | Show unoptimized vector plan (SL)
showDelayedQ :: forall a. QA a => CLOptimizer -> Q a -> IO ()
showDelayedQ clOpt (Q q) = do
    let cl = toComprehensions q
    let vl = compileQ clOpt cl :: QueryPlan VSL DVec
    h <- fileId
    let fileName = "q_vl_" ++ h
    exportPlan fileName vl
    void $ runCommand $ printf "stack exec vsldot -- -i %s.plan | dot -Tpdf -o %s.pdf && open %s.pdf" fileName fileName fileName

-- | Show unoptimized vector plan (SL)
showDelayedOptQ :: forall a. QA a => CLOptimizer -> Q a -> IO ()
showDelayedOptQ clOpt (Q q) = do
    let cl = toComprehensions q
    let vl = compileOptQ clOpt cl :: QueryPlan VSL DVec
    h <- fileId
    let fileName = "q_vl_" ++ h
    exportPlan fileName vl
    void $ runCommand $ printf "stack exec vsldot -- -i %s.plan | dot -Tpdf -o %s.pdf && open %s.pdf" fileName fileName fileName

-- | Show all backend queries produced for the given query
showBackendCodeQ :: forall a b v. (VectorLang v, BackendVector b, QA a, Show b)
                 => BackendCodeGen v b
                 -> Q a
                 -> IO ()
showBackendCodeQ codeGen q = do
    putStrLn sepLine
    forM_ (codeQ codeGen q) $ \code -> do
         putStrLn $ show code
         putStrLn sepLine

  where
    sepLine = replicate 80 '-'
