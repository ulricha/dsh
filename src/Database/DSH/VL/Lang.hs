{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Database.DSH.VL.Lang where

import qualified Data.List.NonEmpty as N
import           Data.Aeson.TH

import           Database.Algebra.Aux
import           Database.Algebra.Dag        (Operator, opChildren, replaceOpChild)
import           Database.Algebra.Dag.Common

import qualified Database.DSH.Common.Lang as L

data RowType = Int 
             | Bool 
             | Double
             | String 
             | Unit
             | Pair RowType RowType
             deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''RowType)

type VLColumn = (L.ColName, RowType)
type DBCol = Int

data VLVal = VLInt Int
           | VLBool Bool
           | VLString String
           | VLDouble Double
           | VLUnit
           deriving (Eq, Ord, Show, Read)

$(deriveJSON defaultOptions ''VLVal)

data Expr = BinApp L.ScalarBinOp Expr Expr
          | UnApp L.ScalarUnOp Expr
          | Column DBCol
          | Constant VLVal
          | If Expr Expr Expr
          deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''Expr)

data AggrFun = AggrSum RowType Expr
             | AggrMin Expr
             | AggrMax Expr
             | AggrAvg Expr
             | AggrAll Expr
             | AggrAny Expr
             | AggrCount
             deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''AggrFun)

data WinFun = WinSum Expr
            | WinMin Expr
            | WinMax Expr
            | WinAvg Expr
            | WinAll Expr
            | WinAny Expr
            | WinFirstValue Expr
            | WinCount
            deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''WinFun)


-- | Specification of a window for the window aggregate operator.
data FrameSpec = -- | All elements up to and including the current
                 -- element are in the window
                 FAllPreceding
                 -- | All n preceding elements up to and including the
                 -- current one.
               | FNPreceding Int
                deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''FrameSpec)

--------------------------------------------------------------------------------
-- Vector Language operators. Documentation can be found in module
-- VectorPrimitives.

data NullOp = SingletonDescr
            | Lit (L.Emptiness, [RowType], [[VLVal]])
            | TableRef (String, [VLColumn], L.TableHints)
            deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''NullOp)

data UnOp = UniqueS
          | Number
          | NumberS
          | UnboxRename
          | Segment
          | Unsegment
          | Reverse -- (DBV, PropVector)
          | ReverseS -- (DBV, PropVector)
          | R1
          | R2
          | R3
          | Project [Expr]
          | Select Expr
          | SelectPos1 (L.ScalarBinOp, Int)
          | SelectPos1S (L.ScalarBinOp, Int)
          | GroupAggr ([Expr], N.NonEmpty AggrFun)
          | Aggr AggrFun
          | AggrNonEmpty (N.NonEmpty AggrFun)
          | SortScalarS [Expr]
          | GroupScalarS [Expr]
          | WinFun (WinFun, FrameSpec)
          | Reshape Integer
          | ReshapeS Integer
          | Transpose
    deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''UnOp)

data BinOp = GroupBy    -- (DescrVector, DBV, PropVector)
           | SortS        -- (DBV, PropVector)
           | AggrS AggrFun
           | AggrNonEmptyS (N.NonEmpty AggrFun)
           | DistPrim   -- (DBV, PropVector)
           | DistDesc   -- (DBV, PropVector)
           | Align     -- (DBV, PropVector)
           | PropRename
           | PropFilter -- (DBV, PropVector)
           | PropReorder -- (DBV, PropVector)
           
           -- | Specialized unbox operator that merges DescrToRename
           -- and PropRename. It takes an inner and outer vector, and
           -- pulls the segment that is referenced by the outer vector
           -- into the outer segment. Notice that there must be
           -- /exactly one/ segment referenced by the outer
           -- vector. Inner segments that are not referenced are
           -- silently discarded.
           -- 
           -- Output: @(DVec, RVec)@
           | Unbox
           | Append
           | AppendS
           | Restrict Expr
           | SelectPos L.ScalarBinOp
           | SelectPosS L.ScalarBinOp
           | Zip
           | ZipS
           | CartProduct
           | CartProductS
           | ThetaJoin (L.JoinPredicate Expr)
           | ThetaJoinS (L.JoinPredicate Expr)
           | SemiJoin (L.JoinPredicate Expr)
           | SemiJoinS (L.JoinPredicate Expr)
           | AntiJoin (L.JoinPredicate Expr)
           | AntiJoinS (L.JoinPredicate Expr)
           | NestJoinS (L.JoinPredicate Expr)
           | NestProductS
           | TransposeS
    deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''BinOp)

data TerOp = Combine  -- (DBV, RenameVector, RenameVector)
    deriving (Eq, Ord, Show)

$(deriveJSON defaultOptions ''TerOp)

type VL = Algebra TerOp BinOp UnOp NullOp AlgNode

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
