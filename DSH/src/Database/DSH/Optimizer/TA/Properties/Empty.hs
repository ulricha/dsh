{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Optimizer.TA.Properties.Empty where

import           Database.Algebra.Pathfinder.Data.Algebra

import           Database.DSH.Optimizer.TA.Properties.Types

inferEmptyNullOp :: NullOp -> Empty
inferEmptyNullOp op =
    case op of
        LitTable vs    _   -> null vs
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
        SerializeRel _   -> childEmpty

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
