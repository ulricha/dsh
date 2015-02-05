module Database.DSH.Backend.Sql.Opt.Rewrite.Common where

import qualified Data.IntMap                                   as M

import           Database.Algebra.Dag.Common

import           Database.DSH.Common.QueryPlan

import           Database.DSH.Common.Opt

import           Database.Algebra.Table.Lang

import           Database.DSH.VL.Vector

import           Database.DSH.Backend.Sql.Opt.Properties.BottomUp
import           Database.DSH.Backend.Sql.Opt.Properties.TopDown
import           Database.DSH.Backend.Sql.Opt.Properties.Types

  -- Type abbreviations for convenience
type TARewrite p = Rewrite TableAlgebra (Shape NDVec) p
type TARule p = Rule TableAlgebra p (Shape NDVec)
type TARuleSet p = RuleSet TableAlgebra  p (Shape NDVec)
type TAMatch p = Match TableAlgebra p (Shape NDVec)

inferBottomUp :: TARewrite (NodeMap BottomUpProps)
inferBottomUp = do
  props <- infer inferBottomUpProperties
  return props

inferAll :: TARewrite (NodeMap AllProps)
inferAll = do
  to <- topsort
  buPropMap <- infer inferBottomUpProperties
  props <- infer (inferAllProperties buPropMap to)
  return props

noProps :: Monad m => m (M.IntMap a)
noProps = return M.empty
