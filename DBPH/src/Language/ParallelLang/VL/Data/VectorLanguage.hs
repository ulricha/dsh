{-# LANGUAGE GADTs #-}
module Language.ParallelLang.VL.Data.VectorLanguage where

import Language.ParallelLang.VL.Data.DBVector
import Language.ParallelLang.Common.Data.Op
import Language.ParallelLang.Common.Data.Type
import Language.ParallelLang.FKL.Data.FKL(TypedColumn, Key)

import Database.Algebra.Dag.Common

type VL = Algebra TerOp BinOp UnOp NullOp AlgNode

data NullOp = SingletonDescr
            | ConstructLiteralValue [Type] [PVal]
            | ConstructLiteralTable [Type] [[PVal]]
            | TableRef String [TypedColumn] [Key]
    deriving (Eq, Ord)

data UnOp = Unique
          | UniqueL
          | NotPrim
          | NotVec
          | LengthA
          | DescToRename
          | ToDescr
          | Segment
          | VecSum Type
          | VecMin
          | VecMinL
          | VecMax
          | VecMaxL
          | ProjectL [DBCol]
          | ProjectA [DBCol]
          | IntegerToDoubleA
          | IntegerToDoubleL
          | ReverseA -- (DBV, PropVector)
          | ReverseL -- (DBV, PropVector)
          | FalsePositions
          | R1 
          | R2
          | R3
    deriving (Eq, Ord)

data BinOp = GroupBy    -- (DescrVector, DBV, PropVector)
           | SortWith   -- (DBV, PropVector)
           | LengthSeg
           | DistPrim   -- (DBV, PropVector)
           | DistDesc   -- (DBV, PropVector)
           | DistLift   -- (DBV, PropVector)
           | PropRename
           | PropFilter -- (DBV, PropVector)
           | PropReorder -- (DBV, PropVector)
           | Append     -- (DBV, RenameVector, RenameVector)
           | RestrictVec -- VL (DBV, RenameVector)
           | BinOp Oper
           | BinOpL Oper
           | VecSumL
           | SelectPos Oper -- (DBV, RenameVector)
           | SelectPosL Oper -- (DBV, RenameVector)
           | PairA
           | PairL
           | ZipL       -- (DBV, RenameVector, RenameVector)
    deriving (Eq, Ord)
    
data TerOp = CombineVec  -- (DBV, RenameVector, RenameVector)
    deriving (Eq, Ord)