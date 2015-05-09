{-# LANGUAGE ExplicitForAll      #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}

-- | Compilation, execution and introspection of queries
module Database.DSH.Compiler
  ( -- * Executing queries
    runQ
  , debugQ
  , codeQ
  ) where

import           Control.Arrow
import qualified Data.Foldable                      as F

import           Database.DSH.Translate.Frontend2CL

import           Database.DSH.Backend
import qualified Database.DSH.CL.Lang               as CL
import           Database.DSH.CL.Opt
import           Database.DSH.Common.QueryPlan
import           Database.DSH.Common.Vector
import           Database.DSH.Execute
import           Database.DSH.Frontend.Internals
import           Database.DSH.NKL.Rewrite
import           Database.DSH.Translate.CL2NKL
import           Database.DSH.Translate.FKL2VL
import           Database.DSH.Translate.NKL2FKL
import qualified Database.DSH.VL.Lang               as VL
import           Database.DSH.VL.Opt.OptimizeVL

--------------------------------------------------------------------------------

-- | The backend-independent part of the compiler.
compileQ :: CL.Expr -> QueryPlan VL.VL VLDVec
compileQ = optimizeComprehensions >>>
           desugarComprehensions  >>>
           optimizeNKL            >>>
           flatTransform          >>>
           specializeVectorOps

-- | Compile a query and execute it on a given backend connection.
runQ :: forall a c.
        (Backend c,QA a)
     => c -> Q a -> IO a
runQ c (Q q) = do
    let ty = reify (undefined :: Rep a)
    let cl = toComprehensions q
    let vl = compileQ cl
    let bp = generatePlan $ optimizeVLDefault vl
    let bc = generateCode bp
    frExp <$> execQueryBundle c bc ty

-- | Compile a query and dump intermediate plans to files.
debugQ :: forall a c.(Backend c, QA a)
       => String
       -> c
       -> Q a
       -> IO ()
debugQ prefix _ (Q q) = do
    let cl = toComprehensions q
    let vl = compileQ cl
    let vlOpt = optimizeVLDefault vl
    exportPlan (prefix ++ "_vl") vl
    exportPlan (prefix ++ "_vl_opt") vlOpt
    let bp = generatePlan vlOpt :: BackendPlan c
    dumpPlan prefix bp

-- | Compile a query to the actual backend code that will be executed
-- (for benchmarking purposes).
codeQ :: forall a c.(Backend c, QA a)
      => c
      -> Q a
      -> [BackendCode c]
codeQ _ (Q q) =
    let vl    = optimizeVLDefault $ compileQ $ toComprehensions q
        plan  = generatePlan vl :: BackendPlan c
        shape = generateCode plan :: Shape (BackendCode c)
    in F.foldr (:) [] shape
