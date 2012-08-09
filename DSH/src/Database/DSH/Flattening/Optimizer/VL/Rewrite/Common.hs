module Optimizer.VL.Rewrite.Common where

import Database.Algebra.Dag.Common

import Database.Algebra.VL.Data
import Database.Algebra.Rewrite

import Optimizer.Common.Match
import Optimizer.Common.Rewrite
import Optimizer.VL.Properties.BottomUp
import Optimizer.VL.Properties.Types
  
  -- Type abbreviations for convenience
type VLRewrite a = OptRewrite VL a
type VLRule a = Rule OptRewrite VL a
type VLRuleSet a = RuleSet OptRewrite VL a
  
inferBottomUp :: VLRewrite (NodeMap BottomUpProps)
inferBottomUp = do
  to <- topsort
  props <- infer (inferBottomUpProperties to)
  return props
  