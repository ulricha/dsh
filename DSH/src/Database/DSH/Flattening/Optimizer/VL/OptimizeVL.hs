module Optimizer.VL.OptimizeVL where

import Data.Functor
import Control.Applicative

import Database.Algebra.Dag
import Database.Algebra.Rewrite
import Database.Algebra.VL.Data
  
import Optimizer.VL.Rewrite.PruneEmpty
import Optimizer.VL.Rewrite.MergeProjections
--import Optimizer.VL.Rewrite.Card
import Optimizer.VL.Rewrite.Redundant
import Optimizer.VL.Rewrite.Specialized
import Optimizer.VL.Rewrite.DescriptorModifiers

type RewriteClass = DagRewrite VL Bool

rewriteClasses :: [(Char, RewriteClass)]
rewriteClasses = [ ('E', pruneEmpty) 
                 , ('P', mergeProjections)
                 , ('R', removeRedundancy) 
                 , ('S', introduceSpecializedOperators) 
                 , ('D', stripFromRoot) ]

defaultPipeline :: [RewriteClass]
defaultPipeline = case assemblePipeline "EPRSP" of
  Just p -> p
  Nothing -> error "invalid default pipeline"
  
cleanup :: DagRewrite VL Bool
cleanup = pruneUnusedM >> return True
  
runPipeline :: AlgebraDag VL -> [RewriteClass] -> (AlgebraDag VL, Log)
runPipeline d pipeline = (d', rewriteLog)
  where (d', _, rewriteLog) = runRewrite (sequence_ pipeline) d

assemblePipeline :: String -> Maybe [RewriteClass]
assemblePipeline s = (++) <$> (mapM (flip lookup rewriteClasses) s) <*> (pure [cleanup])
