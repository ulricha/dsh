module Optimizer.VL.Rewrite.Common where

import Database.Algebra.Dag.Common

import Database.Algebra.Rewrite
import Database.Algebra.VL.Data

import Optimizer.VL.Properties.BottomUp
import Optimizer.VL.Properties.Types

inferBottomUp :: DagRewrite VL (NodeMap BottomUpProps)
inferBottomUp = do
  to <- topsortM
  props <- inferM (inferBottomUpProperties to)
  return props
  