module Optimizer.VL.Rewrite.Common where

import qualified Data.Map as M

import Database.Algebra.Dag
import Database.Algebra.Dag.Common

import Database.Algebra.VL.Data
import qualified Database.Algebra.Rewrite as R

import Optimizer.Common.Match
import Optimizer.Common.Rewrite
import Optimizer.VL.Properties.BottomUp
import Optimizer.VL.Properties.TopDown
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
  
inferTopDown :: VLRewrite (NodeMap TopDownProps)
inferTopDown = do
  to <- R.topsort
  buPropMap <- R.infer (inferBottomUpProperties to)
  props <- R.infer (inferTopDownProperties buPropMap to)
  return props
  
inferProperties :: VLRewrite (NodeMap Properties)
inferProperties = do
  bu <- inferBottomUp
  td <- inferTopDown
  return $ M.intersectionWith Properties bu td
  
noProps :: Monad m => m (M.Map k a)
noProps = return M.empty
