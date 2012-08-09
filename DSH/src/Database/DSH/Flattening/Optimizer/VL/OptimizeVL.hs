module Optimizer.VL.OptimizeVL where

import Data.Functor
import Control.Applicative

import qualified Database.Algebra.Dag as Dag
import Database.Algebra.Rewrite
import Database.Algebra.VL.Data
  
import Optimizer.VL.Rewrite.PruneEmpty
import Optimizer.VL.Rewrite.MergeProjections
import Optimizer.VL.Rewrite.Redundant
import Optimizer.VL.Rewrite.Specialized
import Optimizer.VL.Rewrite.Expressions
import Optimizer.VL.Rewrite.DescriptorModifiers

type RewriteClass = DefaultRewrite VL Bool

rewriteClasses :: [(Char, RewriteClass)]
rewriteClasses = [ ('E', pruneEmpty) 
                 , ('P', mergeProjections)
                 , ('R', removeRedundancy) 
                 , ('C', optExpressions)
                 , ('S', introduceSpecializedOperators) 
                 , ('D', stripFromRoot) ]

defaultPipeline :: [RewriteClass]
defaultPipeline = case assemblePipeline "ERSRSD" of
  Just p -> p
  Nothing -> error "invalid default pipeline"
  
cleanup :: DefaultRewrite VL Bool
cleanup = pruneUnused >> return True
  
runPipeline :: Dag.AlgebraDag VL -> [RewriteClass] -> (Dag.AlgebraDag VL, Log)
runPipeline d pipeline = (d', rewriteLog)
  where (d', _, rewriteLog) = runDefaultRewrite (sequence_ pipeline) d

assemblePipeline :: String -> Maybe [RewriteClass]
assemblePipeline s = (++) <$> (mapM (flip lookup rewriteClasses) s) <*> (pure [cleanup])
