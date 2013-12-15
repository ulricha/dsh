{-# LANGUAGE TemplateHaskell #-}

-- | Infer the output schema of TableAlgebra operators.
module Database.DSH.Optimizer.TA.Properties.Cols where

import qualified Data.Set.Monad as S

import           Database.DSH.Impossible

import           Database.Algebra.Pathfinder.Data.Algebra

inferColsNullOp :: NullOp -> S.Set AttrName
inferColsNullOp op = 
    case op of
        LitTable _ schema      -> S.fromList $ map fst schema
        EmptyTable schema      -> S.fromList $ map fst schema
        TableRef (_, attrs, _) -> S.fromList $ map (\(_, c, _) -> c) attrs

inferColsUnOp :: S.Set AttrName -> UnOp -> S.Set AttrName
inferColsUnOp childCols op =
    case op of
        RowNum (resCol, _, _) -> S.insert resCol childCols
        RowRank (resCol, _)   -> S.insert resCol childCols
        Rank (resCol, _)      -> S.insert resCol childCols
        Project projs         -> S.fromList $ map fst projs
        Select _              -> childCols
        Distinct _            -> childCols
        Aggr (acols, mpcol)   -> (S.fromList $ map snd acols) `S.union` (maybe S.empty S.singleton mpcol)
        PosSel _              -> $impossible

inferColsBinOp :: S.Set AttrName -> S.Set AttrName -> BinOp -> S.Set AttrName
inferColsBinOp leftCols rightCols op =
    case op of
        Cross _      -> S.union leftCols rightCols
        EqJoin _     -> S.union leftCols rightCols
        ThetaJoin _  -> S.union leftCols rightCols
        SemiJoin _   -> S.union leftCols rightCols
        AntiJoin _   -> S.union leftCols rightCols
        DisjUnion _  -> leftCols
        Difference _ -> leftCols
        
        
        
