{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Backend.Sql.Opt.Properties.Empty where

import           Database.Algebra.Table.Lang

import           Database.DSH.Backend.Sql.Opt.Properties.Types

inferEmptyNullOp :: NullOp -> Empty
inferEmptyNullOp op =
    case op of
        LitTable (vs, _)   -> null vs
        TableRef (_, _, _) -> False

inferEmptyUnOp :: Empty -> UnOp -> Empty
inferEmptyUnOp childEmpty op =
    case op of
        WinFun _         -> childEmpty
        RowNum (_, _, _) -> childEmpty
        RowRank (_, _)   -> childEmpty
        Rank (_, _)      -> childEmpty
        Project _        -> childEmpty
        Select _         -> childEmpty
        Distinct _       -> childEmpty
        Aggr (_, _)      -> childEmpty
        Serialize    _   -> childEmpty

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
