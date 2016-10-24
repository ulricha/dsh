{-# LANGUAGE CPP #-}

module Database.DSH.VSL.Opt.OptimizeVSL where

import qualified Data.IntMap                                                      as M

import qualified Database.Algebra.Dag                                             as Dag

import           Database.DSH.Common.QueryPlan

import           Database.DSH.VSL.Lang
import           Database.DSH.Common.Vector

import           Database.DSH.Common.Opt
import           Database.DSH.Common.VectorLang
import           Database.DSH.VSL.Opt.Rewrite.Expressions
import           Database.DSH.VSL.Opt.Rewrite.PruneEmpty
import           Database.DSH.VSL.Opt.Rewrite.Redundant

type RewriteClass = Rewrite (VSLOp TExpr TExpr) (Shape DVec) Bool

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
  :: Dag.AlgebraDag TVSL
  -> (Shape DVec)
  -> [RewriteClass]
  -> Bool -> (Dag.AlgebraDag TVSL, Log, Shape DVec)
runPipeline d sh pipeline debug = (Dag.dmap VSL d', rewriteLog, sh')
  where (d', sh', _, rewriteLog) = runRewrite (sequence_ pipeline) (Dag.dmap unVSL d) sh debug

assemblePipeline :: String -> Maybe [RewriteClass]
assemblePipeline s = mapM (flip lookup rewriteClasses) s

optimizeSL :: [RewriteClass] -> QueryPlan TVSL DVec -> QueryPlan TVSL DVec
optimizeSL pipeline plan =
#ifdef DEBUGGRAPH
  let (d, _, shape) = runPipeline (queryDag plan) (queryShape plan) pipeline True
#else
  let (d, _, shape) = runPipeline (queryDag plan) (queryShape plan) pipeline False
#endif
  in QueryPlan { queryDag = d, queryShape = shape, queryTags = M.empty }

optimizeSL' :: [RewriteClass] -> QueryPlan TVSL DVec -> (QueryPlan TVSL DVec, Log)
optimizeSL' pipeline plan =
  let (d, l, shape) = runPipeline (queryDag plan) (queryShape plan) pipeline False
  in (QueryPlan { queryDag = d, queryShape = shape, queryTags = M.empty }, l)

optimizeVSLDefault :: QueryPlan TVSL DVec -> QueryPlan TVSL DVec
optimizeVSLDefault = optimizeSL defaultPipeline
