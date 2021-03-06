{-# LANGUAGE CPP #-}

module Database.DSH.SL.Opt.OptimizeSL where

import qualified Data.IntMap                                                      as M

import qualified Database.Algebra.Dag                                             as Dag

import           Database.DSH.Common.QueryPlan

import           Database.DSH.SL.Lang
import           Database.DSH.Common.Vector

import           Database.DSH.Common.Opt
import           Database.DSH.Common.VectorLang
import           Database.DSH.SL.Opt.Rewrite.Projections
import           Database.DSH.SL.Opt.Rewrite.PruneEmpty
import           Database.DSH.SL.Opt.Rewrite.Redundant

type RewriteClass = Rewrite (SLOp TExpr TExpr) (Shape DVec) Bool

rewriteClasses :: [(Char, RewriteClass)]
rewriteClasses = [ ('E', pruneEmpty)
                 , ('R', removeRedundancy)
                 , ('C', optExpressions)
                 ]

defaultPipeline :: [RewriteClass]
defaultPipeline = case assemblePipeline "ER" of
  Just p -> p
  Nothing -> error "invalid default pipeline"

runPipeline :: Dag.AlgebraDag TSL
            -> (Shape DVec)
            -> [RewriteClass]
            -> Bool
            -> (Dag.AlgebraDag TSL, Log, Shape DVec)
runPipeline d sh pipeline debug = (Dag.dmap SL d', rewriteLog, sh')
  where (d', sh', _, rewriteLog) = runRewrite (sequence_ pipeline) (Dag.dmap unSL d) sh debug

assemblePipeline :: String -> Maybe [RewriteClass]
assemblePipeline s = mapM (flip lookup rewriteClasses) s

optimizeSL :: [RewriteClass] -> QueryPlan TSL DVec -> QueryPlan TSL DVec
optimizeSL pipeline plan =
#ifdef DEBUGGRAPH
  let (d, _, shape) = runPipeline (queryDag plan) (queryShape plan) pipeline True
#else
  let (d, _, shape) = runPipeline (queryDag plan) (queryShape plan) pipeline False
#endif
  in QueryPlan { queryDag = d, queryShape = shape, queryTags = M.empty }

optimizeSL' :: [RewriteClass] -> QueryPlan TSL DVec -> (QueryPlan TSL DVec, Log)
optimizeSL' pipeline plan =
  let (d, l, shape) = runPipeline (queryDag plan) (queryShape plan) pipeline False
  in (QueryPlan { queryDag = d, queryShape = shape, queryTags = M.empty }, l)

optimizeSLDefault :: QueryPlan TSL DVec -> QueryPlan TSL DVec
optimizeSLDefault = optimizeSL defaultPipeline
