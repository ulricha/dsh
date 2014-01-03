{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Optimizer.TA.Properties.Empty where

import           Database.DSH.Impossible

import           Database.Algebra.Pathfinder.Data.Algebra

import           Database.DSH.Optimizer.TA.Properties.Types

inferEmptyNullOp :: NullOp -> Empty
inferEmptyNullOp op =
    case op of
        LitTable _    _    -> False
        EmptyTable _       -> True
        TableRef (_, _, _) -> False

inferEmptyUnOp :: Empty -> UnOp -> Empty
inferEmptyUnOp childEmpty op =
    case op of
        RowNum (_, _, _) -> childEmpty
        RowRank (_, _)   -> childEmpty
        Rank (_, _)      -> childEmpty
        Project _        -> childEmpty
        Select _         -> childEmpty
        Distinct _       -> childEmpty
        Aggr (_, _)      -> childEmpty
        PosSel _         -> $impossible

inferEmptyBinOp :: Empty -> Empty -> BinOp -> Empty
inferEmptyBinOp leftEmpty rightEmpty op =
    case op of
        Cross _      -> leftEmpty || rightEmpty
        EqJoin _     -> leftEmpty || rightEmpty
        ThetaJoin _  -> leftEmpty || rightEmpty
        SemiJoin _   -> leftEmpty
        AntiJoin _   -> False
        DisjUnion _  -> False
        Difference _ -> False
