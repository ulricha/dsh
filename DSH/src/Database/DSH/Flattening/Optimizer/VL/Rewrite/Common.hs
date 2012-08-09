module Optimizer.VL.Rewrite.Common where

import Database.Algebra.Dag.Common

import Database.Algebra.Rewrite
import Database.Algebra.VL.Data

import Optimizer.VL.Properties.BottomUp
import Optimizer.VL.Properties.Types
  
-- Type abbreviation for convenience
type VLRewrite a = DefaultRewrite VL a
type VLRule a = Rule DefaultRewrite VL a
type VLRuleSet a = RuleSet DefaultRewrite VL a
  
inferBottomUp :: VLRewrite (NodeMap BottomUpProps)
inferBottomUp = do
  to <- topsort
  props <- infer (inferBottomUpProperties to)
  return props
  