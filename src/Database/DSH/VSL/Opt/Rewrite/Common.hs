{-# LANGUAGE TemplateHaskell #-}
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
type VSLRewrite p = R.Rewrite VSL (Shape DVec) p
type VSLRule p = R.Rule VSL p (Shape DVec)
type VSLRuleSet p = R.RuleSet VSL p (Shape DVec)
type VSLMatch p = R.Match VSL p (Shape DVec)

inferBottomUp :: VSLRewrite (NodeMap BottomUpProps)
inferBottomUp = do
  to    <- R.topsort
  props <- R.infer $ inferBottomUpProperties to
  return props

inferTopDown :: VSLRewrite (NodeMap TopDownProps)
inferTopDown = do
  to        <- R.topsort
  buPropMap <- R.infer $ inferBottomUpProperties to
  props     <- R.infer (inferTopDownProperties buPropMap to)
  return props

inferProperties :: VSLRewrite (NodeMap Properties)
inferProperties = do
  buMap <- inferBottomUp
  tdMap <- inferTopDown
  return $ M.intersectionWith Properties buMap tdMap

noProps :: Monad m => m (M.IntMap a)
noProps = return M.empty

---------------------------------------------------------------------------------
-- Rewrite helper functions

lookupR1Parents :: AlgNode -> VSLRewrite [AlgNode]
lookupR1Parents q = R.parents q >>= \ps -> filterM isR1 ps
  where
    isR1 :: AlgNode -> VSLRewrite Bool
    isR1 q' = do
        o <- R.operator q'
        case o of
            UnOp R1 _ -> return True
            _         -> return False


lookupR2Parents :: AlgNode -> VSLRewrite [AlgNode]
lookupR2Parents q = R.parents q >>= \ps -> filterM isR2 ps
  where
    isR2 :: AlgNode -> VSLRewrite Bool
    isR2 q' = do
        o <- R.operator q'
        case o of
            UnOp R2 _ -> return True
            _         -> return False

-- | Unwrap a constant value
constVal :: Monad m => (L.ScalarVal -> a) -> ConstPayload -> m a
constVal wrap (ConstPL val) = return $ wrap val
constVal _             _    = fail "no match"
