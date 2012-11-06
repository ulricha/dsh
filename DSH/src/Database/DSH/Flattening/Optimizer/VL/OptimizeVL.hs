module Optimizer.VL.OptimizeVL where

import           Control.Applicative

import qualified Database.Algebra.Dag                     as Dag
import           Database.Algebra.Rewrite
import           Database.Algebra.VL.Data

import           Optimizer.Common.Shape
import           Optimizer.VL.Rewrite.DescriptorModifiers
import           Optimizer.VL.Rewrite.Expressions
import           Optimizer.VL.Rewrite.MergeProjections
import           Optimizer.VL.Rewrite.PruneEmpty
import           Optimizer.VL.Rewrite.Redundant
import           Optimizer.VL.Rewrite.Specialized
import           Optimizer.VL.Rewrite.ToDescr

type RewriteClass = Rewrite VL Shape Bool

rewriteClasses :: [(Char, RewriteClass)]
rewriteClasses = [ ('E', pruneEmpty)
                 , ('P', mergeProjections)
                 , ('R', removeRedundancy)
                 , ('C', optExpressions)
                 , ('S', introduceSpecializedOperators)
                 , ('T', pruneColumns)
                 , ('D', stripFromRoot) ]

defaultPipeline :: [RewriteClass]
defaultPipeline = case assemblePipeline "ERSRSD" of
  Just p -> p
  Nothing -> error "invalid default pipeline"

cleanup :: Rewrite VL Shape Bool
cleanup = pruneUnused >> return True

runPipeline :: Dag.AlgebraDag VL -> Shape -> [RewriteClass] -> (Dag.AlgebraDag VL, Log, Shape)
runPipeline d sh pipeline = (d', rewriteLog, sh')
  where (d', sh', _, rewriteLog) = runRewrite (sequence_ pipeline) d sh

assemblePipeline :: String -> Maybe [RewriteClass]
assemblePipeline s = (++) <$> (mapM (flip lookup rewriteClasses) s) <*> (pure [cleanup])
