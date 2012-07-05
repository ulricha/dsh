module Optimizer.VL.Properties.Empty where

import Database.Algebra.VL.Data

inferEmptyNullOp :: NullOp -> Bool
inferEmptyNullOp op =
  case op of
    SingletonDescr              -> False
    ConstructLiteralTable _ []  -> True
    ConstructLiteralTable _ _   -> False
    ConstructLiteralValue _ []  -> True
    ConstructLiteralValue _ _   -> False
    TableRef              _ _ _ -> False
    
inferEmptyUnOp :: Bool -> UnOp -> Bool
inferEmptyUnOp e op =
  case op of
    Unique -> e
    UniqueL -> e
    NotPrim -> e
    NotVec -> e
    LengthA -> False
    DescToRename -> e
    ToDescr -> e
    Segment -> e
    VecSum _ -> False
    VecMin -> e
    VecMinL -> e
    VecMax -> e
    VecMaxL -> e
    ProjectL _ -> e
    ProjectA _ -> e
    IntegerToDoubleA -> e
    IntegerToDoubleL -> e
    ReverseA -> e
    ReverseL -> e
    FalsePositions -> e
    R1 -> e
    R2 -> e
    R3 -> e
    
inferEmptyBinOp :: Bool -> Bool -> BinOp -> Bool
inferEmptyBinOp e1 e2 op =
  case op of
    GroupBy -> e1 || e2
    SortWith -> e1 || e2
    LengthSeg -> undefined
    DistPrim -> e1 || e2
    DistDesc -> e1 || e2
    DistLift -> e1 || e2
    PropRename -> e1 || e2
    PropFilter -> e1 || e2
    PropReorder -> e1 || e2
    Append -> e1 && e2
    RestrictVec -> e1 || e2
    VecBinOp _ -> e1 || e2
    VecBinOpL _ -> e1 || e2
    VecSumL -> e1 && e2 -- FIXME check if correct
    SelectPos _ -> e1 || e2
    SelectPosL _ -> e1 || e2
    PairA -> e1 || e2
    PairL -> e1 || e2
    ZipL -> e1 || e2
    
inferEmptyTerOp :: Bool -> Bool -> Bool -> TerOp -> Bool
inferEmptyTerOp e1 e2 e3 op =
  case op of
    -- FIXME conjunction holds only for the first component of the output.
    -- the other ones are already empty if their respective input is empty
    CombineVec -> e1 && e2 && e3 
    
