module Optimizer.VL.Properties.Width where

import Database.Algebra.VL.Data

inferWidthNullOp :: NullOp -> Int
inferWidthNullOp op =
  case op of
    SingletonDescr              -> 0
    ConstructLiteralTable _ _   -> 0 -- FIXME
    ConstructLiteralValue _ _   -> 0 -- FIXME
    TableRef              _ cols _ -> length cols
    
inferWidthUnOp :: Int -> UnOp -> Int
inferWidthUnOp w op =
  case op of
    Unique -> w
    UniqueL -> w
    NotPrim -> 1
    NotVec -> 1
    LengthA -> 1
    DescToRename -> 0
    ToDescr -> 0
    Segment -> -1
    VecSum _ -> 1
    VecMin -> 1
    VecMinL -> 1
    VecMax -> 1
    VecMaxL -> 1
    ProjectL cols -> length cols
    ProjectA cols -> length cols
    IntegerToDoubleA -> 1
    IntegerToDoubleL -> 1
    ReverseA -> w
    ReverseL -> w
    FalsePositions -> -1
    R1 -> w
    R2 -> w
    R3 -> w
    
inferWidthBinOp :: Int -> Int -> BinOp -> Int
inferWidthBinOp w1 w2 op =
  case op of
    GroupBy -> 0 -- FIXME this is not correct
    SortWith -> w1
    LengthSeg -> 1
    DistPrim -> w1
    DistDesc -> w1
    DistLift -> w1
    PropRename -> w2
    PropFilter -> w2
    PropReorder -> w2
    Append -> w1
    RestrictVec -> w1
    VecBinOp _ -> 1
    VecBinOpL _ -> 1
    VecSumL -> 1
    SelectPos _ -> w1
    SelectPosL _ -> w1
    PairA -> w1 + w2
    PairL -> w1 + w2
    ZipL -> w1 + w2
    
inferWidthTerOp :: Int -> Int -> Int -> TerOp -> Int
inferWidthTerOp w1 _ _ op =
  case op of
    CombineVec -> w1
    
