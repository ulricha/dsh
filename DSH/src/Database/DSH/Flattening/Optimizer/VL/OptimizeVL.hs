module Optimizer.VL.OptimizeVL where

import Data.Functor
import Control.Applicative

import qualified Database.Algebra.Dag as Dag
import Database.Algebra.Rewrite
import Database.Algebra.VL.Data

import Optimizer.Common.Rewrite
import Optimizer.Common.Shape
import Optimizer.VL.Rewrite.PruneEmpty
import Optimizer.VL.Rewrite.MergeProjections
import Optimizer.VL.Rewrite.Redundant
import Optimizer.VL.Rewrite.Specialized
import Optimizer.VL.Rewrite.Expressions
import Optimizer.VL.Rewrite.DescriptorModifiers

type RewriteClass = OptRewrite VL Bool

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
  
cleanup :: OptRewrite VL Bool
cleanup = pruneUnused >> return True
  
runPipeline :: Dag.AlgebraDag VL -> Shape -> [RewriteClass] -> (Dag.AlgebraDag VL, Log, Shape)
runPipeline d sh pipeline = (d', rewriteLog, sh')
  where (d', sh', rewriteLog) = runOptRewrite (sequence_ pipeline) sh d

assemblePipeline :: String -> Maybe [RewriteClass]
assemblePipeline s = (++) <$> (mapM (flip lookup rewriteClasses) s) <*> (pure [cleanup])
