{-# LANGUAGE RankNTypes, GADTs, TypeSynonymInstances, FlexibleInstances, DeriveGeneric #-}
module Language.ParallelLang.VL.Data.VectorLanguage where

import Language.ParallelLang.VL.Data.DBVector
import Language.ParallelLang.Common.Data.Op
import Language.ParallelLang.Common.Data.Type
import Language.ParallelLang.FKL.Data.FKL(TypedColumn, Key)

import GHC.Generics (Generic)

import Database.Algebra.Dag.Common as C
import Database.Algebra.Dag (Operator(..))
import Database.Algebra.Aux

type VL = Algebra TerOp BinOp UnOp NullOp AlgNode

data NullOp = SingletonDescr
            | ConstructLiteralValue [Type] [PVal]
            | ConstructLiteralTable [Type] [[PVal]]
            | TableRef String [TypedColumn] [Key]
    deriving (Eq, Ord, Generic)

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
    deriving (Eq, Ord, Generic)

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
    deriving (Eq, Ord, Generic)
    
data TerOp = CombineVec  -- (DBV, RenameVector, RenameVector)
    deriving (Eq, Ord, Generic)

instance Operator VL where
    opChildren (TerOp _ c1 c2 c3) = [c1, c2, c3]
    opChildren (C.BinOp _ c1 c2) = [c1, c2]
    opChildren (UnOp _ c) = [c]
    opChildren (NullaryOp _) = []

    replaceOpChild oper old new = replaceChild old new oper
     where
         replaceChild :: forall t b u n c. Eq c => c -> c -> Algebra t b u n c -> Algebra t b u n c
         replaceChild o n (TerOp op c1 c2 c3) = TerOp op (replace o n c1) (replace o n c2) (replace o n c3)
         replaceChild o n (C.BinOp op c1 c2) = C.BinOp op (replace o n c1) (replace o n c2)
         replaceChild o n (UnOp op c) = UnOp op (replace o n c)
         replaceChild _ _ (NullaryOp op) = NullaryOp op