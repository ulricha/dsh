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

data NullOp = Lit (PType (), VecSegs)
            | TableRef (String, L.BaseTableSchema)
            deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''NullOp)

data UnOp r e = UnboxKey
              | Segment
              | Unsegment
              | R1
              | R2
              | R3
              | Project r
              | Select e
              | GroupAggr (r, AggrFun e)
              | Number
              | Unique
              | Reverse
              | Sort r
              | Group r
              | WinFun (WinFun e, FrameSpec)
              deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''UnOp)

data BinOp e = ReplicateNest
             | ReplicateScalar
             | ReplicateVector

             | AppKey
             | AppSort
             | AppFilter
             | AppRep

             | UnboxSng
             | Align

             | Fold (AggrFun e)
             | Append
             | Zip
             | CartProduct
             | ThetaJoin (L.JoinPredicate e)
             | SemiJoin (L.JoinPredicate e)
             | AntiJoin (L.JoinPredicate e)
             | NestJoin (L.JoinPredicate e)
             | GroupJoin (L.JoinPredicate e, L.NE (AggrFun e))
    deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''BinOp)

data TerOp = Combine  -- (DBV, RenameVector, RenameVector)
    deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''TerOp)

--------------------------------------------------------------------------------

type SLOp r e = Algebra TerOp (BinOp e) (UnOp r e) NullOp AlgNode

newtype SL r e = SL
    { unSL :: SLOp r e
    } deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''SL)

instance Ordish r e => Operator (SL r e) where
    opChildren = opChildren . unSL
    replaceOpChild (SL a) n1 n2 = SL (replaceOpChild a n1 n2)

type TSL = SL TExpr TExpr
type RSL = SL VRow RExpr
