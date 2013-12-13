module Database.DSH.Optimizer.TA.Rewrite.Common where

import qualified Data.IntMap                                              as M

import           Database.Algebra.Dag.Common

import           Database.DSH.Common.Data.QueryPlan

import           Database.DSH.Optimizer.Common.Rewrite

import           Database.Algebra.Pathfinder.Data.Algebra

import           Database.DSH.Optimizer.TA.Properties.BottomUp
import           Database.DSH.Optimizer.TA.Properties.TopDown
import           Database.DSH.Optimizer.TA.Properties.Types

  -- Type abbreviations for convenience
type TARewrite p = Rewrite PFAlgebra TopShape p
type TARule p = Rule PFAlgebra p TopShape
type TARuleSet p = RuleSet PFAlgebra  p TopShape
type TAMatch p = Match PFAlgebra p TopShape

inferBottomUp :: TARewrite (NodeMap BottomUpProps)
inferBottomUp = do
  props <- infer inferBottomUpProperties
  return props

inferTopDown :: TARewrite (NodeMap TopDownProps)
inferTopDown = do
  to <- topsort
  buPropMap <- infer inferBottomUpProperties
  props <- infer (inferTopDownProperties buPropMap to)
  return props

noProps :: Monad m => m (M.IntMap a)
noProps = return M.empty
