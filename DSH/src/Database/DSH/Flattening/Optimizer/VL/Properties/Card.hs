module Optimizer.VL.Properties.Card where

import Debug.Trace

import Database.Algebra.VL.Data

inferCardOneNullOp :: NullOp -> Bool
inferCardOneNullOp op =
  case op of
    SingletonDescr                -> False
    ConstructLiteralTable _ _     -> False
    ConstructLiteralValue _ _     -> True
    TableRef              _ _ _   -> False

inferCardOneUnOp :: Bool -> UnOp -> Bool
inferCardOneUnOp c op = 
  case op of
    Unique -> c
    UniqueL -> c
    NotPrim -> c
    NotVec -> c
    LengthA -> False
    DescToRename -> c
    ToDescr -> c
    Segment -> c
    VecSum _ -> c
    VecMin -> True
    VecMinL -> c
    VecMax -> True
    VecMaxL -> c
    ProjectL _ -> c
    ProjectA _ -> c
    IntegerToDoubleA -> c
    IntegerToDoubleL -> c
    ReverseA -> c
    ReverseL -> c
    FalsePositions -> c
    R1 -> c
    R2 -> c
    R3 -> c

inferCardOneBinOp :: Bool -> Bool -> BinOp -> Bool
inferCardOneBinOp c1 c2 op =
  case op of
    GroupBy -> False
    SortWith -> False
    LengthSeg -> False
    DistPrim -> False
    DistDesc -> False
    DistLift -> False
    PropRename -> False
    PropFilter -> False
    PropReorder -> False
    Append -> False
    RestrictVec -> False
    VecBinOp _ -> False
    VecBinOpL _ -> False
    VecSumL -> False
    SelectPos _ -> False
    SelectPosL _ -> False
    PairA -> False
    PairL -> False
    ZipL -> False

inferCardOneTerOp :: Bool -> Bool -> Bool -> TerOp -> Bool
inferCardOneTerOp _ _ _ op =
  case op of
    CombineVec -> False
