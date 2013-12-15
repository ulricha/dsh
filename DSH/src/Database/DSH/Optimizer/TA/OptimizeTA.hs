module Database.DSH.Optimizer.TA.OptimizeTA where

import           Debug.Trace

import qualified Data.IntMap as M

import qualified Database.Algebra.Dag                                             as Dag

import           Database.Algebra.Pathfinder.Data.Algebra

import           Database.DSH.Common.Data.QueryPlan

import           Database.DSH.Optimizer.Common.Rewrite

import           Database.DSH.Optimizer.TA.Rewrite.Basic

import           Database.DSH.Optimizer.TA.Properties.TopDown
import           Database.DSH.Optimizer.TA.Properties.BottomUp

{-

rough plan/first goals:

merge projections: no properties, leads to basic infrastructure

prune unreferenced rownums: icols prop

simplify rownums, e.g. key-based: key prop, maybe fd (not sure if necessary)

merge sorting criteria into rownums:  track sorting criteria

remove rownums if concrete values not required: use prop, key prop, ?

-}

type RewriteClass = Rewrite PFAlgebra TopShape Bool

defaultPipeline :: [RewriteClass]
defaultPipeline = [cleanup]

runPipeline :: Dag.AlgebraDag PFAlgebra 
            -> TopShape 
            -> [RewriteClass] 
            -> Bool 
            -> (Dag.AlgebraDag PFAlgebra, Log, TopShape)
runPipeline d sh pipeline debug = (d', rewriteLog, sh')
  where (d', sh', _, rewriteLog) = runRewrite (sequence_ pipeline) d sh debug

optimizeTA :: QueryPlan PFAlgebra -> QueryPlan PFAlgebra
optimizeTA plan =
  let (d, log, shape) = runPipeline (queryDag plan) (queryShape plan) defaultPipeline True
  in QueryPlan { queryDag = d, queryShape = shape, queryTags = M.empty }
