{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- | Definition of the Virtual Segment Language (VSL). The Virtual Segment
-- Language defines operations over flat vectors that might be *delayed*, i.e.
-- consist of *virtual segments*.
--
-- Data vectors might be either *materialized* (a 1:1 correspondence between
-- virtual and physical segments), *delayed* (virtual segments map to physical
-- segments) or *unit* (all virtual segments map to the unit segment).
module Database.DSH.VSL.Lang where

import           Data.Aeson.TH
import qualified Data.List.NonEmpty             as N

import           Database.Algebra.Dag           (Operator, opChildren,
                                                 replaceOpChild)
import           Database.Algebra.Dag.Common

import qualified Database.DSH.Common.Lang       as L
import           Database.DSH.Common.Type
import           Database.DSH.Common.VectorLang

--------------------------------------------------------------------------------
-- Operator definition

data NullOp = Lit ([ScalarType], SegFrame, Segments)
            | TableRef (String, L.BaseTableSchema)
            deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''NullOp)

data UnOp = SegmentMergeMap
          | Segment
          | Unsegment
          | Nest

          | R1
          | R2
          | R3

          | Project [Expr]
          | Select Expr

          | GroupAggr ([Expr], N.NonEmpty AggrFun)
          | Aggr (N.NonEmpty AggrFun)
          | Number
          | Distinct
          | Reverse
          | Sort [Expr]
          | Group [Expr]
          | WinFun (WinFun, FrameSpec)

          -- | Generate a segment map that statically refers to the unit segment
          | RepUnit
          -- | Update a segment map to statically refer to the unit segment.
          -- Used as the update operation for unit delayed vectors for which we
          -- need only the outermost segment map.
          | UnitMap
    deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''UnOp)

data BinOp = ReplicateSeg
           | ReplicateScalar

           | AppKey
           | AppSort
           | AppFilter
           | AppRep

           | UnboxSng
           | UnboxDefault (N.NonEmpty Expr)
           | Align

           | AggrSeg AggrFun
           | Append
           | Zip
           | CartProduct

           | ThetaJoinMM (L.JoinPredicate Expr)
           | ThetaJoinMU (L.JoinPredicate Expr)
           | ThetaJoinUM (L.JoinPredicate Expr)

           | AntiJoinMM (L.JoinPredicate Expr)
           | AntiJoinMU (L.JoinPredicate Expr)
           | AntiJoinUM (L.JoinPredicate Expr)

           | SemiJoinMM (L.JoinPredicate Expr)
           | SemiJoinMU (L.JoinPredicate Expr)
           | SemiJoinUM (L.JoinPredicate Expr)

           | GroupJoinMM (L.JoinPredicate Expr, L.NE AggrFun)
           | GroupJoinMU (L.JoinPredicate Expr, L.NE AggrFun)
           | GroupJoinUM (L.JoinPredicate Expr, L.NE AggrFun)

           -- Operators overloaded on the vector representation
           -- M: materialized
           -- D: delayed
           -- U: unit
           | NestJoinMM (L.JoinPredicate Expr)
           | NestJoinMU (L.JoinPredicate Expr)

           -- Maintenance operations on virtual segments

           -- | Materialize a delayed vector according to a segment map.
           -- Produces a materialized data vector as well as a replication
           -- vector for any inner vectors
           | Materialize
           -- | Materialize a delayed vector according to a segment map in which
           -- every entry points to the unit segment.
           -- Produces a materialized data vector as well as a replication
           -- vector for any inner vectors
           | MaterializeUnit
           -- | Update a segment map by combining it with another segment map
           -- from the left (form the composition of two index space transforms)
           | UpdateMap
           -- | 
           | RepMap
    deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''BinOp)

data TerOp = Combine  -- (DBV, RenameVector, RenameVector)
    deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''TerOp)

--------------------------------------------------------------------------------
-- DAG-based representation of VSL programs

type VSL = Algebra TerOp BinOp UnOp NullOp AlgNode

checkRep :: Eq a => a -> a -> a -> a
checkRep orig new x = if x == orig then new else x

instance Operator VSL where
    opChildren (TerOp _ c1 c2 c3) = [c1, c2, c3]
    opChildren (BinOp _ c1 c2) = [c1, c2]
    opChildren (UnOp _ c) = [c]
    opChildren (NullaryOp _) = []

    replaceOpChild oper old new = replaceChild old new oper
      where
        replaceChild :: forall t b u n c. Eq c => c -> c -> Algebra t b u n c -> Algebra t b u n c
        replaceChild o n (TerOp op c1 c2 c3) = TerOp op (checkRep o n c1) (checkRep o n c2) (checkRep o n c3)
        replaceChild o n (BinOp op c1 c2) = BinOp op (checkRep o n c1) (checkRep o n c2)
        replaceChild o n (UnOp op c) = UnOp op (checkRep o n c)
        replaceChild _ _ (NullaryOp op) = NullaryOp op
