 module Optimizer.VL.OptimizeVL where

import Database.Algebra.Dag
import Database.Algebra.Rewrite
import Database.Algebra.VL.Data
  
import Optimizer.VL.Rewrite.PruneEmpty
import Optimizer.VL.Rewrite.MergeProjections

type RewriteClass = DagRewrite VL Bool

rewriteClasses :: [(Char, RewriteClass)]
rewriteClasses = [ ('E', pruneEmpty) 
                 , ('P', mergeProjections) ]

defaultPipeline :: [RewriteClass]
defaultPipeline = case assemblePipeline "E" of
  Just p -> p
  Nothing -> error "invalid default pipeline"
  
runPipeline :: AlgebraDag VL -> [RewriteClass] -> (AlgebraDag VL, Log)
runPipeline d pipeline = (d', rewriteLog)
  where (d', _, rewriteLog) = runRewrite (sequence_ pipeline) d

assemblePipeline :: String -> Maybe [RewriteClass]
assemblePipeline s = mapM (flip lookup rewriteClasses) s
