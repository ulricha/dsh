{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Database.DSH.VSL.Opt.Rewrite.Common where

import qualified Data.IntMap                              as M

import           Control.Monad

import           Database.Algebra.Dag.Common

import           Database.DSH.Common.QueryPlan

import qualified Database.DSH.Common.Lang                 as L
import qualified Database.DSH.Common.Opt                  as R
import           Database.DSH.Common.Vector
import           Database.DSH.Common.VectorLang
import           Database.DSH.VSL.Lang

import           Database.DSH.VSL.Opt.Properties.BottomUp
import           Database.DSH.VSL.Opt.Properties.TopDown
import           Database.DSH.VSL.Opt.Properties.Types

  -- Type abbreviations for convenience
type VSLRewrite r e p = R.Rewrite (VSLOp r e) (Shape DVec) p
type VSLRule r e p    = R.Rule (VSLOp r e) p (Shape DVec)
type VSLRuleSet r e p = R.RuleSet (VSLOp r e) p (Shape DVec)
type VSLMatch r e p   = R.Match (VSLOp r e) p (Shape DVec)

inferBottomUp :: Ordish r e => VSLRewrite r e (NodeMap BottomUpProps)
inferBottomUp = do
  to    <- R.topsort
  props <- R.infer $ inferBottomUpProperties to
  return props

inferTopDown :: Ordish r e => VSLRewrite r e (NodeMap TopDownProps)
inferTopDown = do
  to        <- R.topsort
  buPropMap <- R.infer $ inferBottomUpProperties to
  props     <- R.infer (inferTopDownProperties buPropMap to)
  return props

inferProperties :: Ordish r e => VSLRewrite r e (NodeMap Properties)
inferProperties = do
  buMap <- inferBottomUp
  tdMap <- inferTopDown
  return $ M.intersectionWith Properties buMap tdMap

noProps :: Monad m => m (M.IntMap a)
noProps = return M.empty

---------------------------------------------------------------------------------
-- Rewrite helper functions

lookupR1Parents :: forall r e . Ordish r e => AlgNode -> VSLRewrite r e [AlgNode]
lookupR1Parents q = R.parents q >>= \ps -> filterM isR1 ps
  where
    isR1 :: AlgNode -> VSLRewrite r e Bool
    isR1 q' = do
        o <- R.operator q'
        case o of
            UnOp R1 _ -> return True
            _         -> return False


lookupR2Parents :: forall r e . Ordish r e => AlgNode -> VSLRewrite r e [AlgNode]
lookupR2Parents q = R.parents q >>= \ps -> filterM isR2 ps
  where
    isR2 :: AlgNode -> VSLRewrite r e Bool
    isR2 q' = do
        o <- R.operator q'
        case o of
            UnOp R2 _ -> return True
            _         -> return False

-- | Unwrap a constant value
constVal :: Monad m => (L.ScalarVal -> a) -> ConstPayload -> m a
constVal wrap (ConstPL val) = return $ wrap val
constVal _             _    = fail "no match"
