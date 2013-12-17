{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Optimizer.TA.Properties.Empty where

import qualified Data.Set.Monad as S

import           Database.DSH.Impossible

import           Database.Algebra.Pathfinder.Data.Algebra

import           Database.DSH.Optimizer.TA.Properties.Types

inferEmptyNullOp :: NullOp -> Empty
inferEmptyNullOp op =
    case op of
        LitTable vals _    -> False
        EmptyTable _       -> True
        TableRef (_, _, _) -> False

inferEmptyUnOp :: Empty -> Empty -> UnOp -> Empty
inferEmptyUnOp childEmpty childEmpty op =
    case op of
        RowNum (resCol, _, _)   -> childEmpty
        RowRank (resCol, _)     -> childEmpty
        Rank (resCol, _)        -> childEmpty
        Project projs           -> childEmpty
        Select _                -> childEmpty
        Distinct _              -> childEmpty
        Aggr (acols, Just gcol) -> childEmpty
        Aggr (acols, Nothing)   -> childEmpty
        PosSel _                -> $impossible

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
