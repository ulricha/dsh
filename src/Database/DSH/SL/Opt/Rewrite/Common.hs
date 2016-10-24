{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Database.DSH.SL.Opt.Rewrite.Common where

import qualified Data.IntMap                             as M

import           Control.Monad

import           Database.Algebra.Dag.Common

import           Database.DSH.Common.QueryPlan

import qualified Database.DSH.Common.Opt                 as R
import           Database.DSH.Common.Vector
import           Database.DSH.Common.VectorLang
import           Database.DSH.SL.Lang

import           Database.DSH.SL.Opt.Properties.BottomUp
import           Database.DSH.SL.Opt.Properties.TopDown
import           Database.DSH.SL.Opt.Properties.Types

  -- Type abbreviations for convenience
type SLRewrite r e p = R.Rewrite (SLOp r e) (Shape DVec) p
type SLRule r e p = R.Rule (SLOp r e) p (Shape DVec)
type SLRuleSet r e p = R.RuleSet (SLOp r e) p (Shape DVec)
type SLMatch r e p = R.Match (SLOp r e) p (Shape DVec)

inferBottomUp :: Ordish r e => SLRewrite r e (NodeMap BottomUpProps)
inferBottomUp = do
  to    <- R.topsort
  props <- R.infer $ inferBottomUpProperties to
  return props

-- FIXME replace infer with exposeDag
inferTopDown :: Ordish r e => SLRewrite r e (NodeMap TopDownProps)
inferTopDown = do
  to        <- R.topsort
  buPropMap <- R.infer (inferBottomUpProperties to)
  props     <- R.infer (inferTopDownProperties buPropMap to)
  return props

-- FIXME this infers bottom up properties twice!
inferProperties :: Ordish r e => SLRewrite r e (NodeMap Properties)
inferProperties = do
  buMap <- inferBottomUp
  tdMap <- inferTopDown
  return $ M.intersectionWith Properties buMap tdMap

noProps :: Monad m => m (M.IntMap a)
noProps = return M.empty

---------------------------------------------------------------------------------
-- Rewrite helper functions

lookupR1Parents :: forall r e. Ordish r e => AlgNode -> SLRewrite r e [AlgNode]
lookupR1Parents q = R.parents q >>= \ps -> filterM isR1 ps
  where
    isR1 :: AlgNode -> SLRewrite r e Bool
    isR1 q' = do
        o <- R.operator q'
        case o of
            UnOp R1 _ -> return True
            _         -> return False


lookupR2Parents :: forall r e . Ordish r e => AlgNode -> SLRewrite r e [AlgNode]
lookupR2Parents q = R.parents q >>= \ps -> filterM isR2 ps
  where
    isR2 :: AlgNode -> SLRewrite r e Bool
    isR2 q' = do
        o <- R.operator q'
        case o of
            UnOp R2 _ -> return True
            _         -> return False

