{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PatternSynonyms #-}

module Database.DSH.SL.Opt.Rewrite.Common where

import qualified Data.IntMap                             as M

import           Control.Monad
import           Data.List.NonEmpty                   (NonEmpty ((:|)))

import           Database.Algebra.Dag.Common

import           Database.DSH.Common.QueryPlan

import           Database.DSH.Common.Impossible
import qualified Database.DSH.Common.Lang                as L
import           Database.DSH.Common.Nat
import qualified Database.DSH.Common.Opt                 as R
import           Database.DSH.Common.Vector
import           Database.DSH.Common.VectorLang
import           Database.DSH.SL.Lang

import           Database.DSH.SL.Opt.Properties.BottomUp
import           Database.DSH.SL.Opt.Properties.TopDown
import           Database.DSH.SL.Opt.Properties.Types

  -- Type abbreviations for convenience
type SLRewrite p = R.Rewrite SL (Shape DVec) p
type SLRule p = R.Rule SL p (Shape DVec)
type SLRuleSet p = R.RuleSet SL p (Shape DVec)
type SLMatch p = R.Match SL p (Shape DVec)

inferBottomUp :: SLRewrite (NodeMap BottomUpProps)
inferBottomUp = do
  to    <- R.topsort
  props <- R.infer $ inferBottomUpProperties to
  return props

-- FIXME replace infer with exposeDag
inferTopDown :: SLRewrite (NodeMap TopDownProps)
inferTopDown = do
  to        <- R.topsort
  buPropMap <- R.infer (inferBottomUpProperties to)
  props     <- R.infer (inferTopDownProperties buPropMap to)
  return props

-- FIXME this infers bottom up properties twice!
inferProperties :: SLRewrite (NodeMap Properties)
inferProperties = do
  buMap <- inferBottomUp
  tdMap <- inferTopDown
  return $ M.intersectionWith Properties buMap tdMap

noProps :: Monad m => m (M.IntMap a)
noProps = return M.empty

---------------------------------------------------------------------------------
-- Rewrite helper functions

lookupR1Parents :: AlgNode -> SLRewrite [AlgNode]
lookupR1Parents q = R.parents q >>= \ps -> filterM isR1 ps
  where
    isR1 :: AlgNode -> SLRewrite Bool
    isR1 q' = do
        o <- R.operator q'
        case o of
            UnOp R1 _ -> return True
            _         -> return False


lookupR2Parents :: AlgNode -> SLRewrite [AlgNode]
lookupR2Parents q = R.parents q >>= \ps -> filterM isR2 ps
  where
    isR2 :: AlgNode -> SLRewrite Bool
    isR2 q' = do
        o <- R.operator q'
        case o of
            UnOp R2 _ -> return True
            _         -> return False

