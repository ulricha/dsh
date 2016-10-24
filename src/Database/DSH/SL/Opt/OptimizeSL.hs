{-# LANGUAGE CPP #-}

module Database.DSH.SL.Opt.OptimizeSL where

import qualified Data.IntMap                                                      as M

import qualified Database.Algebra.Dag                                             as Dag

import           Database.DSH.Common.QueryPlan

import           Database.DSH.SL.Lang
import           Database.DSH.Common.Vector

import           Database.DSH.Common.Opt
import           Database.DSH.SL.Opt.Rewrite.Expressions
import           Database.DSH.SL.Opt.Rewrite.PruneEmpty
import           Database.DSH.SL.Opt.Rewrite.Redundant

type RewriteClass = Rewrite RSL (Shape DVec) Bool

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
  :: Dag.AlgebraDag RSL
  -> (Shape DVec)
  -> [RewriteClass]
  -> Bool -> (Dag.AlgebraDag RSL, Log, Shape DVec)
runPipeline d sh pipeline debug = (d', rewriteLog, sh')
  where (d', sh', _, rewriteLog) = runRewrite (sequence_ pipeline) d sh debug

assemblePipeline :: String -> Maybe [RewriteClass]
assemblePipeline s = mapM (flip lookup rewriteClasses) s

optimizeSL :: [RewriteClass] -> QueryPlan RSL DVec -> QueryPlan RSL DVec
optimizeSL pipeline plan =
#ifdef DEBUGGRAPH
  let (d, _, shape) = runPipeline (queryDag plan) (queryShape plan) pipeline True
#else
  let (d, _, shape) = runPipeline (queryDag plan) (queryShape plan) pipeline False
#endif
  in QueryPlan { queryDag = d, queryShape = shape, queryTags = M.empty }

optimizeSL' :: [RewriteClass] -> QueryPlan RSL DVec -> (QueryPlan RSL DVec, Log)
optimizeSL' pipeline plan =
  let (d, l, shape) = runPipeline (queryDag plan) (queryShape plan) pipeline False
  in (QueryPlan { queryDag = d, queryShape = shape, queryTags = M.empty }, l)

optimizeSLDefault :: QueryPlan RSL DVec -> QueryPlan RSL DVec
optimizeSLDefault = optimizeSL defaultPipeline
