module Database.DSH.Flattening.Optimizer.VL.Rewrite.Common where

import qualified Data.IntMap                                              as M

import           Database.Algebra.Dag.Common

import           Database.Algebra.Rewrite
import           Database.Algebra.VL.Data

import           Database.DSH.Flattening.Optimizer.Common.Shape
import           Database.DSH.Flattening.Optimizer.VL.Properties.BottomUp
import           Database.DSH.Flattening.Optimizer.VL.Properties.TopDown
import           Database.DSH.Flattening.Optimizer.VL.Properties.Types

  -- Type abbreviations for convenience
type VLRewrite p = Rewrite VL Shape p
type VLRule p = Rule VL p Shape
type VLRuleSet p = RuleSet VL p Shape

inferBottomUp :: VLRewrite (NodeMap BottomUpProps)
inferBottomUp = do
  props <- infer inferBottomUpProperties
  return props

inferTopDown :: VLRewrite (NodeMap TopDownProps)
inferTopDown = do
  to <- topsort
  buPropMap <- infer inferBottomUpProperties
  props <- infer (inferTopDownProperties buPropMap to)
  return props

inferProperties :: VLRewrite (NodeMap Properties)
inferProperties = do
  buMap <- inferBottomUp
  tdMap <- inferTopDown
  return $ M.intersectionWith Properties buMap tdMap

noProps :: Monad m => m (M.IntMap a)
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

relinkParentsWithShape :: AlgNode -> AlgNode -> Rewrite VL Shape ()
relinkParentsWithShape old new = do
  replaceRootWithShape old new
  relinkParents old new
