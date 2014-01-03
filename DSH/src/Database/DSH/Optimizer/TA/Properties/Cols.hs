{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE MonadComprehensions #-}

-- | Infer the output schema of TableAlgebra operators.
module Database.DSH.Optimizer.TA.Properties.Cols where

import qualified Data.Set.Monad as S

import           Database.DSH.Impossible

import           Database.Algebra.Pathfinder.Data.Algebra

import Database.DSH.Optimizer.TA.Properties.Aux
import Database.DSH.Optimizer.TA.Properties.Types

----------------------------------------------------------------------------
-- Type inference for tablealgebra expressions

isNumeric :: BinFun -> Bool
isNumeric f = f `elem` [Plus, Minus, Times, Div]

isComp :: BinFun -> Bool
isComp f = f `elem` [Gt, Lt, LtE, GtE, Eq, Contains, SimilarTo, Like]

isBool :: BinFun -> Bool
isBool f = f `elem` [And, Or]

binAppTy :: BinFun -> ATy -> ATy -> ATy
binAppTy f t1 _t2 =
    case f of
        f | isComp f    -> ABool
        f | isBool f    -> ABool
        f | isNumeric f -> t1
        Modulo          -> AInt
        Concat          -> AStr

unAppTy :: UnFun -> ATy
unAppTy Not      = ABool
unAppTy (Cast t) = t

valType :: AVal -> ATy
valType (VInt _)    = AInt
valType (VStr _)    = AStr
valType (VBool _)   = ABool
valType (VDouble _) = ADouble
valType (VDec _)    = ADec
valType (VNat _)    = ANat

exprTy :: S.Set TypedAttr -> Expr -> ATy
exprTy childCols expr = 
    case expr of
        ColE c          -> typeOf c childCols
        ConstE v        -> valType v
        BinAppE f e1 e2 -> binAppTy f (exprTy childCols e1) (exprTy childCols e2)
        UnAppE f e      -> unAppTy f

----------------------------------------------------------------------------
-- Type inference for aggregate functions

aggrTy :: S.Set TypedAttr -> (AggrType, AttrName) -> TypedAttr
aggrTy childCols (aggr, resCol) = (resCol, resType)
  where
    resType = case aggr of
        All _  -> ABool
        Prod _ -> undefined
        Dist _ -> undefined
        Count  -> AInt
        Avg c  -> numAggr (typeOf c childCols)
        Max c  -> numAggr (typeOf c childCols)
        Min c  -> numAggr (typeOf c childCols)
        Sum c  -> numAggr (typeOf c childCols)

    numAggr :: ATy -> ATy
    numAggr AInt = AInt
    numAggr ADec = ADec
    numAggr ANat = ANat
    numAggr _    = $impossible

----------------------------------------------------------------------------
-- Schema inference for tablealgebra operators

inferColsNullOp :: NullOp -> S.Set TypedAttr
inferColsNullOp op = 
    case op of
        LitTable _ schema      -> S.fromList schema
        EmptyTable schema      -> S.fromList schema
        TableRef (_, attrs, _) -> S.fromList attrs

inferColsUnOp :: S.Set TypedAttr -> UnOp -> S.Set TypedAttr
inferColsUnOp childCols op =
    case op of
        RowNum (resCol, _, _) -> S.insert (resCol, AInt) childCols
        RowRank (resCol, _)   -> S.insert (resCol, AInt) childCols
        Rank (resCol, _)      -> S.insert (resCol, AInt) childCols
        Project projs         -> S.fromList $ map (\(c, e) -> (c, exprTy childCols e)) projs
        Select _              -> childCols
        Distinct _            -> childCols
        Aggr (acols, pcols)   -> (S.fromList $ map (aggrTy childCols) acols) 
                                 ∪
                                 [ (c, typeOf c childCols) | c <- S.fromList pcols ]
        PosSel _              -> $impossible

inferColsBinOp :: S.Set TypedAttr -> S.Set TypedAttr -> BinOp -> S.Set TypedAttr
inferColsBinOp leftCols rightCols op =
    case op of
        Cross _      -> S.union leftCols rightCols
        EqJoin _     -> S.union leftCols rightCols
        ThetaJoin _  -> S.union leftCols rightCols
        SemiJoin _   -> S.union leftCols rightCols
        AntiJoin _   -> S.union leftCols rightCols
        DisjUnion _  -> leftCols
        Difference _ -> leftCols
        
        
        
