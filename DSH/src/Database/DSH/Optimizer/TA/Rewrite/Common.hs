module Database.DSH.Optimizer.TA.Rewrite.Common where

import qualified Data.IntMap                                              as M

import           Database.Algebra.Dag.Common

import           Database.DSH.Common.Data.QueryPlan

import           Database.DSH.Optimizer.Common.Rewrite

import           Database.Algebra.Pathfinder.Data.Algebra

  -- Type abbreviations for convenience
type TARewrite p = Rewrite PFAlgebra TopShape p
type TARule p = Rule PFAlgebra p TopShape
type TARuleSet p = RuleSet PFAlgebra  p TopShape
type TAMatch p = Match PFAlgebra p TopShape

noProps :: Monad m => m (M.IntMap a)
noProps = return M.empty
