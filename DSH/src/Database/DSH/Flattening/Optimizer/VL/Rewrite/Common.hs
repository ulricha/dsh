module Optimizer.VL.Rewrite.Common where

import Database.Algebra.Dag
import Database.Algebra.Dag.Common

import Database.Algebra.VL.Data
import qualified Database.Algebra.Rewrite as R

import Optimizer.Common.Match
import Optimizer.Common.Rewrite
import Optimizer.VL.Properties.BottomUp
import Optimizer.VL.Properties.Types
  
  -- Type abbreviations for convenience
type VLRewrite a = OptRewrite VL a
type VLRule a = R.Rule OptMatch OptRewrite VL a
type VLRuleSet a = R.RuleSet OptMatch OptRewrite VL a
  
inferBottomUp :: VLRewrite (NodeMap BottomUpProps)
inferBottomUp = do
  to <- R.topsort
  props <- R.infer (inferBottomUpProperties to)
  return props
  
