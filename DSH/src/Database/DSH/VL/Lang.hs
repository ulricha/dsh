{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Database.DSH.VL.Lang where

import           GHC.Generics                (Generic)

import qualified Data.List.NonEmpty as N

import           Database.Algebra.Aux
import           Database.Algebra.Dag        (Operator, opChildren, replaceOpChild)
import           Database.Algebra.Dag.Common

import qualified Database.DSH.Common.Lang as L

type VL = Algebra TerOp BinOp UnOp NullOp AlgNode

data VLType = Nat | Int | Bool |  Double
            | String | Unit
            | Pair VLType VLType | VLList VLType
            deriving (Eq, Ord, Generic, Show)

type VLColumn = (L.ColName, VLType)
type DBCol = Int

data AggrFun = AggrSum VLType Expr
             | AggrMin Expr
             | AggrMax Expr
             | AggrAvg Expr
             | AggrAll Expr
             | AggrAny Expr
             | AggrCount
               deriving (Eq, Ord, Show, Generic)

data Expr = BinApp L.ScalarBinOp Expr Expr
                | UnApp L.ScalarUnOp Expr
                | Column DBCol
                | Constant VLVal
                | If Expr Expr Expr
                deriving (Eq, Ord, Show, Generic)

newtype Nat = N Int deriving (Eq, Ord, Generic, Show, Read)

instance Integral Nat where
  quot (N i1) (N i2)    = N $ quot i1 i2
  rem (N i1) (N i2)     = N $ rem i1 i2
  div (N i1) (N i2)     = N $ div i1 i2
  mod (N i1) (N i2)     = N $ mod i1 i2
  quotRem (N i1) (N i2) = let (q, r) = quotRem i1 i2 in (N q, N r)
  divMod (N i1) (N i2)  = let (d, m) = divMod i1 i2 in (N d, N m)
  toInteger (N i)       = toInteger i

instance Real Nat where
  toRational (N i) = toRational i

instance Enum Nat where
  toEnum         = N
  fromEnum (N i) = i

instance Num Nat where
  (N i1) + (N i2) = N $ i1 + i2
  (N i1) * (N i2) = N $ i1 * i2
  (N i1) - (N i2) = N $ i1 - i2
  negate (N i)    = N $ negate i
  abs (N i)       = N $ abs i
  signum (N i)    = N $ signum i
  fromInteger i   = N $ fromInteger i

data VLVal = VLInt Int
           | VLNat Nat
           | VLBool Bool
           | VLString String
           | VLDouble Double
           | VLUnit
           deriving (Eq, Ord, Generic, Show, Read)

data NullOp = SingletonDescr
            | Lit L.Emptiness [VLType] [[VLVal]]
            | TableRef String [VLColumn] L.TableHints
            deriving (Eq, Ord, Generic, Show)

data UnOp = UniqueS
          | Number
          | NumberS
          | DescToRename
          | Segment
          | Unsegment
          | Reverse -- (DBV, PropVector)
          | ReverseS -- (DBV, PropVector)
          | R1
          | R2
          | R3
          | Project [Expr]
          | Select Expr
          | SelectPos1 L.ScalarBinOp Nat
          | SelectPos1S L.ScalarBinOp Nat
          | GroupAggr [Expr] (N.NonEmpty AggrFun)
          | Aggr AggrFun
          | AggrNonEmpty (N.NonEmpty AggrFun)
          | SortSimple [Expr]
          | GroupSimple [Expr]
          | Reshape Integer
          | ReshapeS Integer
          | Transpose
    deriving (Eq, Ord, Generic, Show)

data BinOp = GroupBy    -- (DescrVector, DBV, PropVector)
           | Sort        -- (DBV, PropVector)
           | AggrS AggrFun
           | AggrNonEmptyS (N.NonEmpty AggrFun)
           | DistPrim   -- (DBV, PropVector)
           | DistDesc   -- (DBV, PropVector)
           | Align     -- (DBV, PropVector)
           | PropRename
           | PropFilter -- (DBV, PropVector)
           | PropReorder -- (DBV, PropVector)
           | Append     -- (DBV, RenameVector, RenameVector)
           | AppendS
           | Restrict -- VL (DBV, RenameVector)
           | SelectPos L.ScalarBinOp -- (DBV, RenameVector)
           | SelectPosS L.ScalarBinOp -- (DBV, RenameVector)
           | Zip
           | ZipS            -- (DBV, RenameVector, RenameVector)
           | CartProduct
           | CartProductS
           -- FIXME VL joins should include join expressions!
           | ThetaJoin (L.JoinPredicate Expr)
           | ThetaJoinS (L.JoinPredicate Expr)
           | SemiJoin (L.JoinPredicate Expr)
           | SemiJoinS (L.JoinPredicate Expr)
           | AntiJoin (L.JoinPredicate Expr)
           | AntiJoinS (L.JoinPredicate Expr)
           | NestJoinS (L.JoinPredicate Expr)
           | NestProductS
           | TransposeS
    deriving (Eq, Ord, Generic, Show)

data TerOp = Combine  -- (DBV, RenameVector, RenameVector)
    deriving (Eq, Ord, Generic, Show)

instance Operator VL where
    opChildren (TerOp _ c1 c2 c3) = [c1, c2, c3]
    opChildren (BinOp _ c1 c2) = [c1, c2]
    opChildren (UnOp _ c) = [c]
    opChildren (NullaryOp _) = []

    replaceOpChild oper old new = replaceChild old new oper
     where
         replaceChild :: forall t b u n c. Eq c => c -> c -> Algebra t b u n c -> Algebra t b u n c
         replaceChild o n (TerOp op c1 c2 c3) = TerOp op (replace o n c1) (replace o n c2) (replace o n c3)
         replaceChild o n (BinOp op c1 c2) = BinOp op (replace o n c1) (replace o n c2)
         replaceChild o n (UnOp op c) = UnOp op (replace o n c)
         replaceChild _ _ (NullaryOp op) = NullaryOp op
