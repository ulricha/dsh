module Database.DSH.Optimizer.VL.OptimizeVL where

import qualified Data.IntMap                                                      as M

import qualified Database.Algebra.Dag                                             as Dag

import           Database.DSH.Common.QueryPlan

import           Database.DSH.VL.Lang
import           Database.DSH.VL.Vector

import           Database.DSH.Optimizer.Common.Rewrite
import           Database.DSH.Optimizer.VL.Rewrite.Expressions
import           Database.DSH.Optimizer.VL.Rewrite.PruneEmpty
import           Database.DSH.Optimizer.VL.Rewrite.Redundant

type RewriteClass = Rewrite VL (Shape VLDVec) Bool

rewriteClasses :: [(Char, RewriteClass)]
rewriteClasses = [ ('E', pruneEmpty)
                 , ('R', removeRedundancy)
                 , ('C', optExpressions)
                 ]

defaultPipeline :: [RewriteClass]
defaultPipeline = case assemblePipeline "ER" of
  Just p -> p
  Nothing -> error "invalid default pipeline"

runPipeline 
  :: Dag.AlgebraDag VL 
  -> (Shape VLDVec) 
  -> [RewriteClass] 
  -> Bool -> (Dag.AlgebraDag VL, Log, Shape VLDVec)
runPipeline d sh pipeline debug = (d', rewriteLog, sh')
  where (d', sh', _, rewriteLog) = runRewrite (sequence_ pipeline) d sh debug

assemblePipeline :: String -> Maybe [RewriteClass]
assemblePipeline s = mapM (flip lookup rewriteClasses) s

optimizeVL :: [RewriteClass] -> QueryPlan VL VLDVec -> QueryPlan VL VLDVec
optimizeVL pipeline plan =
#ifdef DEBUGGRAPH
  let (d, _, shape) = runPipeline (queryDag plan) (queryShape plan) pipeline True
#else
  let (d, _, shape) = runPipeline (queryDag plan) (queryShape plan) pipeline False
#endif
  in QueryPlan { queryDag = d, queryShape = shape, queryTags = M.empty }

optimizeVL' :: [RewriteClass] -> QueryPlan VL VLDVec -> (QueryPlan VL VLDVec, Log)
optimizeVL' pipeline plan =
  let (d, l, shape) = runPipeline (queryDag plan) (queryShape plan) pipeline False
  in (QueryPlan { queryDag = d, queryShape = shape, queryTags = M.empty }, l)

optimizeVLDefault :: QueryPlan VL VLDVec -> QueryPlan VL VLDVec
optimizeVLDefault = optimizeVL defaultPipeline
