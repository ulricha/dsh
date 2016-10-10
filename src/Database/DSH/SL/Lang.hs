{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- | Definition of the Segment Language (SL): The Segment Language defines
-- operations over flat segment vectors.
module Database.DSH.SL.Lang where

import           Data.Aeson.TH

import           Database.Algebra.Dag.Common

import qualified Database.DSH.Common.Lang       as L
import           Database.DSH.Common.VectorLang


--------------------------------------------------------------------------------
-- Vector Language operators. Documentation can be found in module
-- VectorAlgebra.

data NullOp = Lit (PType, VecSegs)
            | TableRef (String, L.BaseTableSchema)
            deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''NullOp)

data UnOp = UnboxKey
          | Segment
          | Unsegment

          | R1
          | R2
          | R3

          | Project VectorExpr
          | Select VectorExpr

          | GroupAggr (VectorExpr, AggrFun)
          | Number
          | Unique
          | Reverse
          | Sort VectorExpr
          | Group VectorExpr
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

           | Fold AggrFun
           | Append
           | Zip
           | CartProduct
           | ThetaJoin (L.JoinPredicate VectorExpr)
           | SemiJoin (L.JoinPredicate VectorExpr)
           | AntiJoin (L.JoinPredicate VectorExpr)
           | NestJoin (L.JoinPredicate VectorExpr)
           | GroupJoin (L.JoinPredicate VectorExpr, L.NE AggrFun)
    deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''BinOp)

data TerOp = Combine  -- (DBV, RenameVector, RenameVector)
    deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''TerOp)

type SL = Algebra TerOp BinOp UnOp NullOp AlgNode
