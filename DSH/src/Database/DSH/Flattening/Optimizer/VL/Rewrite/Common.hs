module Database.DSH.Flattening.Optimizer.VL.Rewrite.Common where

import qualified Data.IntMap                                              as M

import           Database.Algebra.Dag.Common

import           Database.DSH.Flattening.Common.Data.QueryPlan

import           Database.Algebra.VL.Data
import           Database.DSH.Flattening.Optimizer.Common.Rewrite

import           Database.DSH.Flattening.Optimizer.VL.Properties.BottomUp
import           Database.DSH.Flattening.Optimizer.VL.Properties.TopDown
import           Database.DSH.Flattening.Optimizer.VL.Properties.Types

  -- Type abbreviations for convenience
type VLRewrite p = Rewrite VL TopShape p
type VLRule p = Rule VL p TopShape
type VLRuleSet p = RuleSet VL p TopShape
type VLMatch p = Match VL p TopShape

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
