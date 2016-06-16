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

data UnOp = Segment
          | Unsegment
          | Nest

          | R1
          | R2
          | R3

          | Project [Expr]
          | Select Expr

          | GroupAggr ([Expr], N.NonEmpty AggrFun)
          | Aggr (N.NonEmpty AggrFun)
          | AggrSeg AggrFun
          | Number
          | Distinct
          | Reverse
          | Sort [Expr]
          | Group [Expr]
          | WinFun (WinFun, FrameSpec)

          -- | Generate a segment map that statically refers to the unit segment
          | UnitMap
          -- | Update a segment map to statically refer to the unit segment.
          -- Used as the update operation for unit delayed vectors for which we
          -- need only the outermost segment map.
          | UpdateUnit
          -- From a vector v, generate a *merge map* that maps all segments of
          -- the key domain of v to the segment identifier domain of v.
          | MergeMap
    deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''UnOp)

data SegmentLookup = Direct
                   | Unit
                   deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''SegmentLookup)

data BinOp = ReplicateSeg
           | ReplicateScalar

           | UnboxSng
           | UnboxDefault (N.NonEmpty L.ScalarVal)
           | Align

           | Append
           | Zip
           | CartProduct

           | ThetaJoin (SegmentLookup, SegmentLookup, L.JoinPredicate Expr)

           | AntiJoin (SegmentLookup, SegmentLookup, L.JoinPredicate Expr)

           | SemiJoin (SegmentLookup, SegmentLookup, L.JoinPredicate Expr)

           | GroupJoin (SegmentLookup, SegmentLookup, L.JoinPredicate Expr, L.NE AggrFun)

           | NestJoin (SegmentLookup, SegmentLookup, L.JoinPredicate Expr)

           -- Maintenance operations on virtual segments

           -- | Materialize a delayed vector according to a segment map.
           -- Produces a materialized data vector as well as a replication
           -- vector for any inner vectors
           | Materialize
           -- | Update a segment map by combining it with another segment map
           -- from the left (form the composition of two index space transforms)
           | UpdateMap
    deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''BinOp)

data TerOp = Combine  -- (DBV, RenameVector, RenameVector)
    deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''TerOp)

--------------------------------------------------------------------------------
-- DAG-based representation of VSL programs

type VSL = Algebra TerOp BinOp UnOp NullOp AlgNode
