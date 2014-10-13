{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE TemplateHaskell     #-}

-- | Infer the output schema of TableAlgebra operators.
module Database.DSH.Optimizer.TA.Properties.Cols where

import qualified Data.Set.Monad                             as S


import           Database.Algebra.Table.Lang

import           Database.DSH.Impossible
import           Database.DSH.Optimizer.TA.Properties.Aux
import           Database.DSH.Optimizer.TA.Properties.Types

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
        Gt        -> ABool
        Lt        -> ABool
        LtE       -> ABool
        GtE       -> ABool
        Eq        -> ABool
        NEq       -> ABool
        Contains  -> ABool
        SimilarTo -> ABool
        Like      -> ABool
        And       -> ABool
        Or        -> ABool
        Plus      -> t1
        Minus     -> t1
        Times     -> t1
        Div       -> t1
        Modulo    -> AInt
        Concat    -> AStr

unAppTy :: UnFun -> ATy
unAppTy Not         = ABool
unAppTy (Cast t)    = t
unAppTy Sin         = ADouble
unAppTy Cos         = ADouble
unAppTy Tan         = ADouble
unAppTy ASin        = ADouble
unAppTy ACos        = ADouble
unAppTy ATan        = ADouble
unAppTy Log         = ADouble
unAppTy Sqrt        = ADouble
unAppTy Exp         = ADouble
unAppTy SubString{} = AStr

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
        UnAppE f _      -> unAppTy f
        IfE _ t _       -> exprTy childCols t

----------------------------------------------------------------------------
-- Type inference for aggregate functions

numAggr :: ATy -> ATy
numAggr AInt    = AInt
numAggr ADec    = ADec
numAggr ANat    = ANat
numAggr ADouble = ADouble
numAggr _       = $impossible


aggrTy :: S.Set TypedAttr -> (AggrType, Attr) -> TypedAttr
aggrTy childCols (aggr, resCol) = (resCol, resType)
  where
    resType = case aggr of
        All _  -> ABool
        Any _  -> ABool
        Count  -> AInt
        Avg e  -> numAggr $ exprTy childCols e
        Max e  -> numAggr $ exprTy childCols e
        Min e  -> numAggr $ exprTy childCols e
        Sum e  -> numAggr $ exprTy childCols e

winFunTy :: S.Set TypedAttr -> (WinFun, Attr) -> TypedAttr
winFunTy childCols (aggr, resCol) = (resCol, resType)
  where
    resType = case aggr of
        WinAll _        -> ABool
        WinAny _        -> ABool
        WinCount        -> AInt
        WinAvg e        -> numAggr $ exprTy childCols e
        WinMax e        -> numAggr $ exprTy childCols e
        WinMin e        -> numAggr $ exprTy childCols e
        WinSum e        -> numAggr $ exprTy childCols e
        WinFirstValue e -> exprTy childCols e
        WinLastValue e  -> exprTy childCols e

----------------------------------------------------------------------------
-- Schema inference for tablealgebra operators

inferColsNullOp :: NullOp -> S.Set TypedAttr
inferColsNullOp op =
    case op of
        LitTable _ schema      -> S.fromList schema
        TableRef (_, attrs, _) -> S.fromList attrs

inferColsUnOp :: S.Set TypedAttr -> UnOp -> S.Set TypedAttr
inferColsUnOp childCols op =
    case op of
        WinFun ((resCol, fun), _, _, _) -> S.insert (winFunTy childCols (fun, resCol)) childCols
        RowNum (resCol, _, _) -> S.insert (resCol, AInt) childCols
        RowRank (resCol, _)   -> S.insert (resCol, AInt) childCols
        Rank (resCol, _)      -> S.insert (resCol, AInt) childCols
        Project projs         -> S.fromList $ map (\(c, e) -> (c, exprTy childCols e)) projs
        Select _              -> childCols
        Distinct _            -> childCols
        Aggr (afuns, pexprs)  -> (S.fromList $ map (aggrTy childCols) afuns)
                                 ∪
                                 [ (c, exprTy childCols e) | (c, e) <- S.fromList pexprs ]
        Serialize (md, mp, cs) ->
            let cols = (S.fromList $ map (\(PayloadCol c) -> c) cs)
                       ∪ (maybe S.empty (\(DescrCol c) -> S.singleton c) md)
                       ∪ posCol mp
            in S.map (\c -> (c, typeOf c childCols)) cols

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



