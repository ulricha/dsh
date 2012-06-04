module Optimizer.X100.OptimizeX100(optimize) where

import Control.Monad.State

import Database.Algebra.Graph.Common
import Database.Algebra.Graph.AlgebraDag
import Database.Algebra.X100.Data.Algebra
import Optimizer.Rewrite.ProjectionMerge
import Optimizer.Rewrite.ConstOpt

optimize :: [AlgNode] -> AlgebraDag X100Algebra -> AlgebraDag X100Algebra
optimize roots d =
    dag $ execState pipeline (rewriteState d)
    where pipeline = do
              pruneUnusedM roots
              mergeProjections roots
              optimizeConst roots
              mergeProjections roots
