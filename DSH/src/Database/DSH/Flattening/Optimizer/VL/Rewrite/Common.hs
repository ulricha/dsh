module Optimizer.VL.Rewrite.Common where

import qualified Data.Map as M

import Database.Algebra.Dag.Common

import Database.Algebra.VL.Data
import Database.Algebra.Rewrite

import Optimizer.Common.Shape
import Optimizer.VL.Properties.BottomUp
import Optimizer.VL.Properties.TopDown
import Optimizer.VL.Properties.Types
  
  -- Type abbreviations for convenience
type VLRewrite p = Rewrite VL Shape p
type VLRule p = Rule VL p Shape
type VLRuleSet p = RuleSet VL p Shape
  
inferBottomUp :: VLRewrite (NodeMap BottomUpProps)
inferBottomUp = do
  to <- topsort
  props <- infer (inferBottomUpProperties to)
  return props
  
inferTopDown :: VLRewrite (NodeMap TopDownProps)
inferTopDown = do
  to <- topsort
  buPropMap <- infer (inferBottomUpProperties to)
  props <- infer (inferTopDownProperties buPropMap to)
  return props
  
inferProperties :: VLRewrite (NodeMap Properties)
inferProperties = do
  buMap <- inferBottomUp
  tdMap <- inferTopDown
  return $ M.intersectionWith Properties buMap tdMap
  
noProps :: Monad m => m (M.Map k a)
noProps = return M.empty
        
replaceRootWithShape :: AlgNode -> AlgNode -> VLRewrite ()
replaceRootWithShape oldRoot newRoot = do
  sh <- getExtras                             
  updateExtras $ updateShape oldRoot newRoot sh
  replaceRoot oldRoot newRoot
  
relinkToNewWithShape :: AlgNode -> VL -> Rewrite VL Shape AlgNode
relinkToNewWithShape oldNode newOp = do
  sh <- getExtras                             
  newNode <- relinkToNew oldNode newOp
  updateExtras $ updateShape oldNode newNode sh
  return newNode
