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

mergeExpr :: [(DBCol, Expr)] -> Expr -> Expr
mergeExpr env expr =
    case expr of
        BinApp o e1 e2 -> BinApp o (mergeExpr env e1) (mergeExpr env e2)
        UnApp o e1     -> UnApp o (mergeExpr env e1)
        Column c       -> case lookup c env of
                               Just expr' -> expr'
                               Nothing    -> error $ show c ++ " " ++ show env
        If c t e       -> If (mergeExpr env c) (mergeExpr env t) (mergeExpr env e)
        Constant _     -> expr

-- | Unwrap a constant value
constVal :: Monad m => (L.ScalarVal -> a) -> ConstPayload -> m a
constVal wrap (ConstPL val) = return $ wrap val
constVal _             _    = fail "no match"

mapAggrFun :: (Expr -> Expr) -> AggrFun -> AggrFun
mapAggrFun f (AggrMax e)           = AggrMax $ f e
mapAggrFun f (AggrSum t e)         = AggrSum t $ f e
mapAggrFun f (AggrMin e)           = AggrMin $ f e
mapAggrFun f (AggrAvg e)           = AggrAvg $ f e
mapAggrFun f (AggrAny e)           = AggrAny $ f e
mapAggrFun f (AggrAll e)           = AggrAll $ f e
mapAggrFun _ AggrCount             = AggrCount
mapAggrFun f (AggrCountDistinct e) = AggrCountDistinct $ f e

mapWinFun :: (Expr -> Expr) -> WinFun -> WinFun
mapWinFun f (WinMax e)        = WinMax $ f e
mapWinFun f (WinSum e)        = WinSum $ f e
mapWinFun f (WinMin e)        = WinMin $ f e
mapWinFun f (WinAvg e)        = WinAvg $ f e
mapWinFun f (WinAny e)        = WinAny $ f e
mapWinFun f (WinAll e)        = WinAll $ f e
mapWinFun f (WinFirstValue e) = WinFirstValue $ f e
mapWinFun _ WinCount          = WinCount

mapExprCols :: (DBCol -> DBCol) -> Expr -> Expr
mapExprCols f (BinApp op e1 e2) = BinApp op (mapExprCols f e1) (mapExprCols f e2)
mapExprCols f (UnApp op e)      = UnApp op (mapExprCols f e)
mapExprCols f (Column c)        = Column $ f c
mapExprCols _ (Constant val)    = Constant val
mapExprCols f (If c t e)        = If (mapExprCols f c)
                                     (mapExprCols f t)
                                     (mapExprCols f e)

-- | Helper function: Shift all column indexes in an expression by a certain offset.
shiftExprCols :: Int -> Expr -> Expr
shiftExprCols o = mapExprCols (+ o)
