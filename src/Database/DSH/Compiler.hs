{-# LANGUAGE ExplicitForAll      #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Compilation, execution and introspection of queries
module Database.DSH.Compiler
    ( -- * Compiling and executing queries
      runQ
    , compileOptQ
      -- * Debugging and benchmarking queries
    , debugQ
    , codeQ
    , vectorPlanQ
    , showComprehensionsQ
    , showResugaredQ
    , showComprehensionsOptQ
    , showDesugaredQ
    , showDesugaredOptQ
    , showLiftedQ
    , showLiftedOptQ
    , showFlattenedQ
    , showFlattenedOptQ
    , showVectorizedQ
    , showVectorizedOptQ
      -- * Comprehension optimizers
    , module Database.DSH.CL.Opt
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
import           Database.DSH.Translate.FKL2VL
import           Database.DSH.Translate.NKL2FKL
import qualified Database.DSH.VL.Lang               as VL
import           Database.DSH.VL.Opt.OptimizeVL

--------------------------------------------------------------------------------

-- | The frontend- and backend-independent part of the compiler.
compileQ :: (CL.Expr -> CL.Expr) -> CL.Expr -> QueryPlan VL.VL VLDVec
compileQ clOpt = clOpt >>>
                 desugarComprehensions  >>>
                 optimizeNKL            >>>
                 flatTransform          >>>
                 specializeVectorOps

-- | The frontend- and backend-independent part of the compiler. Compile a
-- comprehension expression into optimized vector plans.
compileOptQ :: CL.Expr -> QueryPlan VL.VL VLDVec
compileOptQ = compileQ optimizeComprehensions >>> optimizeVLDefault

-- | Compile a query and execute it on a given backend connection.
runQ :: forall a c.
        (Backend c,QA a)
     => c -> Q a -> IO a
runQ c (Q q) = do
    let ty = reify (undefined :: Rep a)
    let cl = toComprehensions q
    let vl = compileQ optimizeComprehensions cl
    let bp = generatePlan $ optimizeVLDefault vl
    let bc = generateCode bp
    frExp <$> execQueryBundle c bc ty

--------------------------------------------------------------------------------

-- | Compile a query and dump intermediate plans to files.
debugQ :: forall a c.(Backend c, QA a)
       => String
       -> c
       -> Q a
       -> IO ()
debugQ prefix _ (Q q) = do
    let cl = toComprehensions q
    let vl = compileQ optimizeComprehensions cl
    let vlOpt = optimizeVLDefault vl
    exportPlan (prefix ++ "_vl") vl
    exportPlan (prefix ++ "_vl_opt") vlOpt
    let bp = generatePlan vlOpt :: BackendPlan c
    void $ dumpPlan prefix False bp
    void $ dumpPlan prefix True bp

vectorPlanQ :: forall a. QA a
            => Q a
            -> QueryPlan VL.VL VLDVec
vectorPlanQ (Q q) =
    optimizeVLDefault $ compileQ optimizeComprehensions $ toComprehensions q

-- | Compile a query to the actual backend code that will be executed
-- (for benchmarking purposes).
codeQ :: forall a c.(Backend c, QA a)
      => c
      -> Q a
      -> [BackendCode c]
codeQ _ (Q q) =
    let vl    = optimizeVLDefault $ compileQ optimizeComprehensions $ toComprehensions q
        plan  = generatePlan vl :: BackendPlan c
        shape = generateCode plan :: Shape (BackendCode c)
    in F.foldr (:) [] shape

--------------------------------------------------------------------------------

decorate :: String -> String
decorate msg = sepLine ++ msg ++ "\n" ++ sepLine
  where
    sepLine = replicate 80 '-' ++ "\n"

-- | Show unoptimized comprehensions (CL)
showComprehensionsQ :: forall a.QA a => (CL.Expr -> CL.Expr) -> Q a -> IO ()
showComprehensionsQ clOpt (Q q) = do
    let cl = clOpt $ toComprehensions q
    putStrLn $ decorate $ pp cl

-- | Show resugared comprehensions (CL)
showResugaredQ :: forall a. QA a => Q a -> IO ()
showResugaredQ (Q q) = do
    let cl = resugarComprehensions $ toComprehensions q
    putStrLn $ decorate $ pp cl

-- | Show optimized comprehensions (CL)
showComprehensionsOptQ :: forall a. QA a => Q a -> IO ()
showComprehensionsOptQ (Q q) = do
    let cl = optimizeComprehensions $ toComprehensions q
    putStrLn $ decorate $ pp cl

-- | Show unoptimized desugared iterators (CL)
showDesugaredQ :: forall a. QA a => (CL.Expr -> CL.Expr) -> Q a -> IO ()
showDesugaredQ clOpt (Q q) = do
    let nkl = desugarComprehensions
              $ clOpt
              $ toComprehensions q
    putStrLn $ decorate $ pp nkl

-- | Show optimized desugared iterators (CL)
showDesugaredOptQ :: forall a. QA a => (CL.Expr -> CL.Expr) -> Q a -> IO ()
showDesugaredOptQ clOpt (Q q) = do
    let nkl = optimizeNKL
              $ desugarComprehensions
              $ clOpt
              $ toComprehensions q
    putStrLn $ decorate $ pp nkl

-- | Show unoptimized lifted operators (FKL intermediate)
showLiftedQ :: forall a. QA a => (CL.Expr -> CL.Expr) -> Q a -> IO ()
showLiftedQ clOpt (Q q) = do
    let fkl = liftOperators
              $ optimizeNKL
              $ desugarComprehensions
              $ clOpt
              $ toComprehensions q
    putStrLn $ decorate $ pp fkl

-- | Show optimized lifted operators (FKL intermediate)
showLiftedOptQ :: forall a. QA a => (CL.Expr -> CL.Expr) -> Q a -> IO ()
showLiftedOptQ clOpt (Q q) = do
    let fkl = optimizeFKL
              $ liftOperators
              $ optimizeNKL
              $ desugarComprehensions
              $ clOpt
              $ toComprehensions q
    putStrLn $ decorate $ pp fkl

-- | Show unoptimized flattened query (FKL)
showFlattenedQ :: forall a. QA a => (CL.Expr -> CL.Expr) -> Q a -> IO ()
showFlattenedQ clOpt (Q q) = do
    let fkl = normalizeLifted
              $ optimizeFKL
              $ liftOperators
              $ optimizeNKL
              $ desugarComprehensions
              $ clOpt
              $ toComprehensions q
    putStrLn $ decorate $ pp fkl

-- | Show optimized flattened query (FKL)
showFlattenedOptQ :: forall a. QA a => (CL.Expr -> CL.Expr) -> Q a -> IO ()
showFlattenedOptQ clOpt (Q q) = do
    let fkl = optimizeNormFKL
              $ normalizeLifted
              $ optimizeFKL
              $ liftOperators
              $ optimizeNKL
              $ desugarComprehensions
              $ clOpt
              $ toComprehensions q
    putStrLn $ decorate $ pp fkl

fileId :: IO String
fileId = replicateM 8 (randomRIO ('a', 'z'))

-- | Show unoptimized vector plan (VL)
showVectorizedQ :: forall a. QA a => (CL.Expr -> CL.Expr) -> Q a -> IO ()
showVectorizedQ clOpt (Q q) = do
    let cl = toComprehensions q
    let vl = compileQ clOpt cl
    h <- fileId
    let fileName = "q_vl_" ++ h
    exportPlan fileName vl
    void $ runCommand $ printf "stack exec vldot -- -i %s.plan | dot -Tpdf -o %s.pdf && open %s.pdf" fileName fileName fileName

-- | Show optimized vector plan (VL)
showVectorizedOptQ :: forall a. QA a => (CL.Expr -> CL.Expr) -> Q a -> IO ()
showVectorizedOptQ clOpt (Q q) = do
    let vl = optimizeVLDefault $ compileQ clOpt $ toComprehensions q
    h <- fileId
    let fileName = "q_vl_" ++ h
    exportPlan fileName vl
    void $ runCommand $ printf "stack exec vldot -- -i %s.plan | dot -Tpdf -o %s.pdf && open %s.pdf" fileName fileName fileName
