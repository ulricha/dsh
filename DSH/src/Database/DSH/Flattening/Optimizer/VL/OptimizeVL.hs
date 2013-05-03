module Database.DSH.Flattening.Optimizer.VL.OptimizeVL where

import qualified Data.IntMap                                                      as M

import qualified Database.Algebra.Dag                                             as Dag
import           Database.Algebra.VL.Data

import           Database.DSH.Flattening.Common.Data.QueryPlan

import           Database.DSH.Flattening.Optimizer.Common.Rewrite
import           Database.DSH.Flattening.Optimizer.VL.Rewrite.DescriptorModifiers
import           Database.DSH.Flattening.Optimizer.VL.Rewrite.Expressions
import           Database.DSH.Flattening.Optimizer.VL.Rewrite.MergeProjections
import           Database.DSH.Flattening.Optimizer.VL.Rewrite.PruneEmpty
import           Database.DSH.Flattening.Optimizer.VL.Rewrite.Redundant
import           Database.DSH.Flattening.Optimizer.VL.Rewrite.Specialized
import           Database.DSH.Flattening.Optimizer.VL.Rewrite.ToDescr
import           Database.DSH.Flattening.Optimizer.VL.Rewrite.Aggregation

type RewriteClass = Rewrite VL TopShape Bool

rewriteClasses :: [(Char, RewriteClass)]
rewriteClasses = [ ('E', pruneEmpty)
                 , ('P', mergeProjections)
                 , ('R', removeRedundancy)
                 , ('C', optExpressions)
                 , ('S', introduceSpecializedOperators)
                 , ('T', pruneColumns)
                 , ('G', groupingToAggregation)
                 , ('D', stripFromRoot) ]

defaultPipeline :: [RewriteClass]
defaultPipeline = case assemblePipeline "ESRSRSR" of
  Just p -> p
  Nothing -> error "invalid default pipeline"

runPipeline :: Dag.AlgebraDag VL -> TopShape -> [RewriteClass] -> Bool -> (Dag.AlgebraDag VL, Log, TopShape)
runPipeline d sh pipeline debug = (d', rewriteLog, sh')
  where (d', sh', _, rewriteLog) = runRewrite (sequence_ pipeline) d sh debug

assemblePipeline :: String -> Maybe [RewriteClass]
assemblePipeline s = mapM (flip lookup rewriteClasses) s

optimizeVL :: [RewriteClass] -> QueryPlan VL -> QueryPlan VL
optimizeVL pipeline plan =
  let (d, _, shape) = runPipeline (queryDag plan) (queryShape plan) pipeline False
  in QueryPlan { queryDag = d, queryShape = shape, queryTags = M.empty }

optimizeVL' :: [RewriteClass] -> QueryPlan VL -> (QueryPlan VL, Log)
optimizeVL' pipeline plan =
  let (d, l, shape) = runPipeline (queryDag plan) (queryShape plan) pipeline False
  in (QueryPlan { queryDag = d, queryShape = shape, queryTags = M.empty }, l)

optimizeVLDefault :: QueryPlan VL -> QueryPlan VL
optimizeVLDefault = optimizeVL defaultPipeline
