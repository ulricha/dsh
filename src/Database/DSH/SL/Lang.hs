{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- | Definition of the Segment Language (SL): The Segment Language defines
-- operations over flat segment vectors.
module Database.DSH.SL.Lang where

import           Data.Aeson.TH
import qualified Data.List.NonEmpty             as N

import           Database.Algebra.Dag.Common

import qualified Database.DSH.Common.Lang       as L
import           Database.DSH.Common.Type
import           Database.DSH.Common.VectorLang


--------------------------------------------------------------------------------
-- Vector Language operators. Documentation can be found in module
-- VectorAlgebra.

data NullOp = Lit ([ScalarType], SegFrame, Segments)
            | TableRef (String, L.BaseTableSchema)
            deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''NullOp)

data UnOp = UnboxKey
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
          | Unique
          | Reverse
          | Sort [Expr]
          | Group [Expr]
          | WinFun (WinFun, FrameSpec)
    deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''UnOp)

data BinOp = ReplicateNest
           | ReplicateScalar
           | ReplicateVector

           | AppKey
           | AppSort
           | AppFilter
           | AppRep

           | UnboxSng
           | Align

           | AggrSeg AggrFun
           | Append
           | Zip
           | CartProduct
           | ThetaJoin (L.JoinPredicate Expr)
           | SemiJoin (L.JoinPredicate Expr)
           | AntiJoin (L.JoinPredicate Expr)
           | NestJoin (L.JoinPredicate Expr)
           | GroupJoin (L.JoinPredicate Expr, L.NE AggrFun)
    deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''BinOp)

data TerOp = Combine  -- (DBV, RenameVector, RenameVector)
    deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''TerOp)

type SL = Algebra TerOp BinOp UnOp NullOp AlgNode
