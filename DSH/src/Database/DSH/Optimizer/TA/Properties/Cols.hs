{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE MonadComprehensions #-}

-- | Infer the output schema of TableAlgebra operators.
module Database.DSH.Optimizer.TA.Properties.Cols where

import qualified Data.Set.Monad as S

import           Database.DSH.Impossible

import           Database.Algebra.Pathfinder.Data.Algebra

import Database.DSH.Optimizer.TA.Properties.Aux
import Database.DSH.Optimizer.TA.Properties.Types

exprTy :: S.Set TypedAttr -> Expr -> ATy
exprTy = undefined

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
        Aggr (acols, mpcol)   -> (S.fromList $ map (aggrTy childCols) acols) 
                                 ∪
                                 (maybe S.empty (\c -> S.singleton (c, typeOf c childCols)) mpcol)
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
        
        
        
