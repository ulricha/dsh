module Database.DSH.Flattening.Optimizer.VL.OptimizeVL where

import           Debug.Trace

import qualified Database.Algebra.Dag                                             as Dag
import           Database.Algebra.VL.Data

import           Database.DSH.Flattening.Optimizer.Common.Shape
import           Database.DSH.Flattening.Optimizer.Common.Rewrite
import           Database.DSH.Flattening.Optimizer.VL.Rewrite.DescriptorModifiers
import           Database.DSH.Flattening.Optimizer.VL.Rewrite.Expressions
import           Database.DSH.Flattening.Optimizer.VL.Rewrite.MergeProjections
import           Database.DSH.Flattening.Optimizer.VL.Rewrite.PruneEmpty
import           Database.DSH.Flattening.Optimizer.VL.Rewrite.Redundant
import           Database.DSH.Flattening.Optimizer.VL.Rewrite.Specialized
import           Database.DSH.Flattening.Optimizer.VL.Rewrite.ToDescr

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
defaultPipeline = case assemblePipeline "ESRSRSR" of
  Just p -> p
  Nothing -> error "invalid default pipeline"

runPipeline :: Dag.AlgebraDag VL -> Shape -> [RewriteClass] -> Bool -> (Dag.AlgebraDag VL, Log, Shape)
runPipeline d sh pipeline debug = (d', rewriteLog, sh')
  where (d', sh', _, rewriteLog) = trace (show $ Dag.refCountMap d) $ runRewrite (sequence_ pipeline) d sh debug

assemblePipeline :: String -> Maybe [RewriteClass]
assemblePipeline s = mapM (flip lookup rewriteClasses) s
