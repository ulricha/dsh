module Database.DSH.Optimizer.VL.OptimizeVL where

import qualified Data.IntMap                                                      as M

import qualified Database.Algebra.Dag                                             as Dag
import           Database.Algebra.VL.Data

import           Database.DSH.Common.Data.QueryPlan

import           Database.DSH.Optimizer.Common.Rewrite
import           Database.DSH.Optimizer.VL.Rewrite.Expressions
import           Database.DSH.Optimizer.VL.Rewrite.PruneEmpty
import           Database.DSH.Optimizer.VL.Rewrite.Redundant
import           Database.DSH.Optimizer.VL.Rewrite.Aggregation

type RewriteClass = Rewrite VL TopShape Bool

rewriteClasses :: [(Char, RewriteClass)]
rewriteClasses = [ ('E', pruneEmpty)
                 , ('R', removeRedundancy)
                 , ('C', optExpressions)
                 , ('G', groupingToAggregation)
                 ]

defaultPipeline :: [RewriteClass]
defaultPipeline = case assemblePipeline "ERGR" of
  Just p -> p
  Nothing -> error "invalid default pipeline"

runPipeline :: Dag.AlgebraDag VL -> TopShape -> [RewriteClass] -> Bool -> (Dag.AlgebraDag VL, Log, TopShape)
runPipeline d sh pipeline debug = (d', rewriteLog, sh')
  where (d', sh', _, rewriteLog) = runRewrite (sequence_ pipeline) d sh debug

assemblePipeline :: String -> Maybe [RewriteClass]
assemblePipeline s = mapM (flip lookup rewriteClasses) s

optimizeVL :: [RewriteClass] -> QueryPlan VL -> QueryPlan VL
optimizeVL pipeline plan =
  let (d, _, shape) = runPipeline (queryDag plan) (queryShape plan) pipeline True
  in QueryPlan { queryDag = d, queryShape = shape, queryTags = M.empty }

optimizeVL' :: [RewriteClass] -> QueryPlan VL -> (QueryPlan VL, Log)
optimizeVL' pipeline plan =
  let (d, l, shape) = runPipeline (queryDag plan) (queryShape plan) pipeline False
  in (QueryPlan { queryDag = d, queryShape = shape, queryTags = M.empty }, l)

optimizeVLDefault :: QueryPlan VL -> QueryPlan VL
optimizeVLDefault = optimizeVL defaultPipeline
