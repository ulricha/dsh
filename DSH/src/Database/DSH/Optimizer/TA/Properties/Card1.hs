{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Optimizer.TA.Properties.Card1 where

import qualified Data.Set.Monad as S

import           Database.DSH.Impossible

import           Database.Algebra.Pathfinder.Data.Algebra

import           Database.DSH.Optimizer.TA.Properties.Types

inferCard1NullOp :: NullOp -> Card1
inferCard1NullOp op =
    case op of
        LitTable vals _    -> length vals == 1
        EmptyTable _       -> False
        TableRef (_, _, _) -> False

inferCard1UnOp :: Card1 -> Empty -> UnOp -> Card1
inferCard1UnOp childCard1 childEmpty op =
    case op of
        RowNum (resCol, _, _)   -> childCard1
        RowRank (resCol, _)     -> childCard1
        Rank (resCol, _)        -> childCard1
        Project projs           -> childCard1
        Select _                -> False
        Distinct _              -> childCard1
        Aggr (acols, Just gcol) -> childCard1
        Aggr (acols, Nothing)   -> not childEmpty
        PosSel _                -> $impossible

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

