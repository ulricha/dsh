{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Optimizer.VL.Rewrite.Common where

import qualified Data.IntMap                                              as M
       
import           Control.Monad

import           Database.Algebra.Dag.Common

import           Database.DSH.Impossible
import           Database.DSH.Common.Data.QueryPlan

import           Database.Algebra.VL.Data
import           Database.DSH.Optimizer.Common.Rewrite

import           Database.DSH.Optimizer.VL.Properties.BottomUp
import           Database.DSH.Optimizer.VL.Properties.TopDown
import           Database.DSH.Optimizer.VL.Properties.Types

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

---------------------------------------------------------------------------------
-- Rewrite helper functions

lookupR1Parents :: AlgNode -> VLRewrite [AlgNode]
lookupR1Parents q = do
  let isR1 q' = do
        o <- operator q'
        case o of
          UnOp R1 _ -> return True
          _         -> return False

  ps <- parents q
  filterM isR1 ps

lookupR2Parents :: AlgNode -> VLRewrite [AlgNode]
lookupR2Parents q = do
  let isR2 q' = do
        o <- operator q'
        case o of
          UnOp R2 _ -> return True
          _         -> return False

  ps <- parents q
  filterM isR2 ps

mergeExpr1 :: [(DBCol, Expr1)] -> Expr1 -> Expr1
mergeExpr1 env expr =
    case expr of
        BinApp1 o e1 e2 -> BinApp1 o (mergeExpr1 env e1) (mergeExpr1 env e2)
        UnApp1 o e1     -> UnApp1 o (mergeExpr1 env e1)
        Column1 c       -> case lookup c env of
                               Just expr' -> expr'
                               Nothing    -> $impossible
        _               -> expr
