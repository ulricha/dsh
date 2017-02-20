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

import           Debug.Trace

import           Control.Arrow
import           Control.Monad
import qualified Data.Foldable                      as F
import qualified System.Info                        as Sys
import           System.Process
import           System.Random
import           Text.Printf

import           Database.Algebra.Dag

import           Database.DSH.Backend
import qualified Database.DSH.CL.Lang               as CL
import           Database.DSH.CL.Opt
import           Database.DSH.CL.Typing
import           Database.DSH.Common.Pretty
import           Database.DSH.Common.QueryPlan
import qualified Database.DSH.Common.Type           as Ty
import           Database.DSH.Common.Vector
import           Database.DSH.Common.VectorLang
import           Database.DSH.Execute
import qualified Database.DSH.FKL.Lang              as FKL
import           Database.DSH.FKL.Rewrite
import           Database.DSH.FKL.Typing
import           Database.DSH.Frontend.Internals
import qualified Database.DSH.NKL.Lang              as NKL
import           Database.DSH.NKL.Rewrite
import           Database.DSH.NKL.Typing
import           Database.DSH.SL
import           Database.DSH.SL.Typing
import           Database.DSH.Translate.CL2NKL
import           Database.DSH.Translate.Frontend2CL
import           Database.DSH.Translate.NKL2FKL
import           Database.DSH.Translate.Vectorize
import           Database.DSH.VSL

--------------------------------------------------------------------------------

typeCheck :: Pretty a => Bool -> (a -> Either String Ty.Type) -> String -> a -> a
typeCheck verbose checker label e =
    case checker e of
        Left msg -> error $ printf "Type checking expression\n>>>\n%s\n<<<\nfailed: %s" (pp e) msg
        Right ty -> if verbose then trace (printf "Inferred type (%s): %s" label (pp ty)) e else e

optimizeCLCheck :: Bool -> CLOptimizer -> CL.Expr -> CL.Expr
optimizeCLCheck verbose clOpt = typeCheck verbose inferCLTy "CL" >>> (fst . clOpt) >>> typeCheck verbose inferCLTy "CL opt"

optimizeNKLCheck :: Bool -> NKL.Expr -> NKL.Expr
optimizeNKLCheck verbose = typeCheck verbose inferNKLTy "NKL" >>> optimizeNKL >>> typeCheck verbose inferNKLTy "NKL opt"

optimizeNormFKLCheck :: Bool -> FKL.FExpr -> FKL.FExpr
optimizeNormFKLCheck verbose = typeCheck verbose inferFKLTy "FKL" >>> optimizeNormFKL >>> typeCheck verbose inferFKLTy "FKL opt"

-- | Transform an expression in the Nested Kernel Language into its equivalent
-- Flat Kernel Language expression by means of the flattening transformation.
-- Apply standard optimization rewrites.
flatTransform :: NKL.Expr -> FKL.FExpr
flatTransform = liftOperators        >>>
                optimizeFKL          >>>
                normalizeLifted      >>>
                optimizeNormFKLCheck False

-- | The frontend- and backend-independent part of the compiler.
compileQ :: VectorLang v => CLOptimizer -> CL.Expr -> QueryPlan (v TExpr TExpr) DVec
compileQ clOpt = optimizeCLCheck False clOpt          >>>
                 desugarComprehensions                >>>
                 optimizeNKLCheck False               >>>
                 flatTransform                        >>>
                 typeCheck False inferFKLTy "FKL opt" >>>
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
    let cl = optimizeCLCheck True clOpt $ toComprehensions q
    putStrLn $ decorate $ pp cl

-- | Show comprehensions with an optional optimizer and display the rewriting
-- log (CL)
showComprehensionsLogQ :: CLOptimizer -> Q a -> IO ()
showComprehensionsLogQ clOpt (Q q) = do
    let (cl, rewriteLog) = first (typeCheck True inferCLTy "CL opt")
                           $ clOpt
                           $ typeCheck True inferCLTy "CL"
                           $ toComprehensions q
    putStrLn rewriteLog
    putStrLn $ decorate $ pp cl

-- | Show unoptimized desugared iterators (CL)
showDesugaredQ :: CLOptimizer -> Q a -> IO ()
showDesugaredQ clOpt (Q q) = do
    let nkl = desugarComprehensions
              $ optimizeCLCheck True clOpt
              $ toComprehensions q
    putStrLn $ decorate $ pp nkl

-- | Show optimized desugared iterators (CL)
showDesugaredOptQ :: CLOptimizer -> Q a -> IO ()
showDesugaredOptQ clOpt (Q q) = do
    let nkl = optimizeNKLCheck True
              $ desugarComprehensions
              $ optimizeCLCheck True clOpt
              $ toComprehensions q
    putStrLn $ decorate $ pp nkl

-- | Show unoptimized lifted operators (FKL intermediate)
showLiftedQ :: CLOptimizer -> Q a -> IO ()
showLiftedQ clOpt (Q q) = do
    let fkl = liftOperators
              $ optimizeNKLCheck True
              $ desugarComprehensions
              $ optimizeCLCheck True clOpt
              $ toComprehensions q
    putStrLn $ decorate $ pp fkl

-- | Show optimized lifted operators (FKL intermediate)
showLiftedOptQ :: CLOptimizer -> Q a -> IO ()
showLiftedOptQ clOpt (Q q) = do
    let fkl = optimizeFKL
              $ liftOperators
              $ optimizeNKLCheck True
              $ desugarComprehensions
              $ optimizeCLCheck True clOpt
              $ toComprehensions q
    putStrLn $ decorate $ pp fkl

-- | Show unoptimized flattened query (FKL)
showFlattenedQ :: CLOptimizer -> Q a -> IO ()
showFlattenedQ clOpt (Q q) = do
    let fkl = normalizeLifted
              $ optimizeFKL
              $ liftOperators
              $ optimizeNKLCheck True
              $ desugarComprehensions
              $ optimizeCLCheck True clOpt
              $ toComprehensions q
    putStrLn $ decorate $ pp fkl

-- | Show optimized flattened query (FKL)
showFlattenedOptQ :: CLOptimizer -> Q a -> IO ()
showFlattenedOptQ clOpt (Q q) = do
    let fkl = optimizeNormFKL
              $ normalizeLifted
              $ optimizeFKL
              $ liftOperators
              $ optimizeNKLCheck True
              $ desugarComprehensions
              $ optimizeCLCheck True clOpt
              $ toComprehensions q
    putStrLn $ decorate $ pp fkl

fileId :: IO String
fileId = replicateM 8 (randomRIO ('a', 'z'))

pdfCmd :: String -> String
pdfCmd f =
    case Sys.os of
        "linux"  -> "evince " ++ f
        "darwin" -> "open " ++ f
        sys      -> error $ "pdfCmd: unsupported os " ++ sys

showSLPlan :: QueryPlan TSL DVec -> IO ()
showSLPlan slPlan = do
    prefix <- ("q_sl_" ++) <$> fileId
    exportPlan prefix slPlan
    void $ runCommand $ printf "stack exec sldot -- -i %s.plan | dot -Tpdf -o %s.pdf && %s" prefix prefix (pdfCmd $ prefix ++ ".pdf")

typeCheckSL :: String -> AlgebraDag TSL -> IO ()
typeCheckSL flavor dag =
    case inferSLTypes dag of
        Left msg -> putStrLn $ printf "Type inference failed for %s SL plan\n%s" flavor msg
        Right _  -> putStrLn $ printf "Type inference succesful for %s SL plan" flavor

-- | Show unoptimized vector plan (SL)
showVectorizedQ :: CLOptimizer -> Q a -> IO ()
showVectorizedQ clOpt (Q q) = do
    let cl = toComprehensions q
    let vl = compileQ clOpt cl :: QueryPlan TSL DVec
    typeCheckSL "unoptimized" (queryDag vl)
    showSLPlan vl

-- | Show optimized vector plan (SL)
showVectorizedOptQ :: CLOptimizer -> Q a -> IO ()
showVectorizedOptQ clOpt (Q q) = do
    let vl = compileQ clOpt $ toComprehensions q :: QueryPlan TSL DVec
    typeCheckSL "unoptimized" (queryDag vl)
    let vlOpt = optimizeVectorPlan vl
    typeCheckSL "optimized" (queryDag vlOpt)
    showSLPlan vlOpt

showVSLPlan :: QueryPlan TVSL DVec -> IO ()
showVSLPlan vslPlan = do
    prefix <- ("q_vsl_" ++) <$> fileId
    exportPlan prefix vslPlan
    void $ runCommand $ printf "stack exec vsldot -- -i %s.plan | dot -Tpdf -o %s.pdf && %s" prefix prefix prefix (pdfCmd $ prefix ++ ".pdf")

-- | Show unoptimized vector plan (SL)
showDelayedQ :: CLOptimizer -> Q a -> IO ()
showDelayedQ clOpt (Q q) = do
    let cl = toComprehensions q
    let vl = compileQ clOpt cl :: QueryPlan TVSL DVec
    showVSLPlan vl

-- | Show unoptimized vector plan (SL)
showDelayedOptQ :: CLOptimizer -> Q a -> IO ()
showDelayedOptQ clOpt (Q q) = do
    let cl = toComprehensions q
    let vl = compileOptQ clOpt cl :: QueryPlan TVSL DVec
    showVSLPlan vl

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
