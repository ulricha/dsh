{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Optimizer.TA.Properties.Card1 where

import           Database.Algebra.Table.Lang

import           Database.DSH.Optimizer.TA.Properties.Types

inferCard1NullOp :: NullOp -> Card1
inferCard1NullOp op =
    case op of
        LitTable (vals, _) -> length vals == 1
        TableRef (_, _, _) -> False

inferCard1UnOp :: Card1 -> Empty -> UnOp -> Card1
inferCard1UnOp childCard1 childEmpty op =
    case op of
        WinFun _          -> childCard1
        RowNum (_, _, _)  -> childCard1
        RowRank (_, _)    -> childCard1
        Rank (_, _)       -> childCard1
        Project _         -> childCard1
        Select _          -> False
        Distinct _        -> childCard1
        Aggr (_, _ : _)   -> childCard1
        Aggr (_, [])      -> not childEmpty
        Serialize    _    -> childCard1

inferCard1BinOp :: Card1 -> Card1 -> BinOp -> Card1
inferCard1BinOp leftCard1 rightCard1 op =
    case op of
        Cross _      -> leftCard1 && rightCard1
        EqJoin _     -> False
        ThetaJoin _  -> False
        SemiJoin _   -> False
        AntiJoin _   -> False
        DisjUnion _  -> False
        Difference _ -> False

