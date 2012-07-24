module Optimizer.VL.Properties.Empty where

import Database.Algebra.VL.Data
  
import Optimizer.VL.Properties.Types
  
unpack :: VectorProp Bool -> Bool
unpack (VProp b) = b
unpack _         = error "no single vector in Properties.Empty"
                   
mapUnpack :: VectorProp Bool -> VectorProp Bool -> (Bool -> Bool -> VectorProp Bool) -> VectorProp Bool
mapUnpack = undefined
  
inferEmptyNullOp :: NullOp -> VectorProp Bool
inferEmptyNullOp op =
  case op of
    SingletonDescr              -> VProp False
    ConstructLiteralTable _ []  -> VProp True
    ConstructLiteralTable _ _   -> VProp False
    ConstructLiteralValue _ []  -> VProp True
    ConstructLiteralValue _ _   -> VProp False
    TableRef              _ _ _ -> VProp False
    
inferEmptyUnOp :: VectorProp Bool -> UnOp -> VectorProp Bool
inferEmptyUnOp e op =
  case op of
    Unique -> e
    UniqueL -> e
    NotPrim -> e
    NotVec -> e
    LengthA -> VProp False
    DescToRename -> e
    ToDescr -> e
    Segment -> e
    VecSum _ -> VProp False
    VecMin -> e
    VecMinL -> e
    VecMax -> e
    VecMaxL -> e
    ProjectL _ -> e
    ProjectA _ -> e
    IntegerToDoubleA -> e
    IntegerToDoubleL -> e
    ReverseA -> let ue = unpack e in VPropPair ue ue
    ReverseL -> let ue = unpack e in VPropPair ue ue
    FalsePositions -> e
    R1 -> 
      case e of
        VProp _           -> error "Properties.Empty: not a pair/triple"
        VPropPair b _     -> VProp b
        VPropTriple b _ _ -> VProp b
    R2 ->
      case e of
        VProp _           -> error "Properties.Empty: not a pair/triple"
        VPropPair _ b     -> VProp b
        VPropTriple _ b _ -> VProp b
    R3 ->
      case e of
        VPropTriple _ _ b -> VProp b
        _                 -> error "Properties.Empty: not a triple"
    ProjectRename _  -> e
    ProjectValue _   -> e
    SelectItem       -> e
    Only             -> undefined
    Singleton        -> undefined
    VecBinOpSingle _ -> e
    
inferEmptyBinOp :: VectorProp Bool -> VectorProp Bool -> BinOp -> VectorProp Bool
inferEmptyBinOp e1 e2 op =
  case op of
    GroupBy -> 
      let ue1 = unpack e1 
          ue2 = unpack e2 
      in VPropTriple ue1 (ue1 || ue2) ue1
    SortWith -> undefined
    LengthSeg -> undefined
    DistPrim -> mapUnpack e1 e2 (\ue1 ue2 -> VPropPair (ue1 || ue2) ue2)
    DistDesc -> mapUnpack e1 e2 (\ue1 ue2 -> VPropPair (ue1 || ue2) (ue1 || ue2))
    DistLift -> mapUnpack e1 e2 (\ue1 ue2 -> VPropPair (ue1 || ue2) (ue1 || ue2))
    PropRename -> mapUnpack e1 e2 (\ue1 ue2 -> VProp (ue1 || ue2))
    PropFilter -> mapUnpack e1 e2 (\ue1 ue2 -> VPropPair (ue1 || ue2) (ue1 || ue2))
    PropReorder -> mapUnpack e1 e2 (\ue1 ue2 -> VPropPair (ue1 || ue2) (ue1 || ue2))
    Append -> mapUnpack e1 e2 (\ue1 ue2 -> VPropTriple (ue1 && ue2) ue1 ue2)
    RestrictVec -> mapUnpack e1 e2 (\ue1 ue2 -> VPropPair (ue1 || ue2) (ue1 || ue2))
    VecBinOp _ -> mapUnpack e1 e2 (\ue1 ue2 -> VPropPair (ue1 || ue2) (ue1 || ue2))
    VecBinOpL _ -> mapUnpack e1 e2 (\ue1 ue2 -> VPropPair (ue1 || ue2) (ue1 || ue2))
    VecSumL -> mapUnpack e1 e2 (\ue1 ue2 -> VProp $ ue1 && ue2) -- FIXME check if correct
    SelectPos _ -> mapUnpack e1 e2 (\ue1 ue2 -> VPropPair (ue1 || ue2) (ue1 || ue2))
    SelectPosL _ -> mapUnpack e1 e2 (\ue1 ue2 -> VPropPair (ue1 || ue2) (ue1 || ue2))
    PairA -> mapUnpack e1 e2 (\ue1 ue2 -> VPropPair (ue1 || ue2) (ue1 || ue2))
    PairL -> mapUnpack e1 e2 (\ue1 ue2 -> VPropPair (ue1 || ue2) (ue1 || ue2))
    ZipL -> mapUnpack e1 e2 (\ue1 ue2 -> VPropPair (ue1 || ue2) (ue1 || ue2))
    CartProduct -> mapUnpack e1 e2 (\ue1 ue2 -> VPropPair (ue1 || ue2) (ue1 || ue2))
    ThetaJoin _ -> mapUnpack e1 e2 (\ue1 ue2 -> VPropPair (ue1 || ue2) (ue1 || ue2))
    
inferEmptyTerOp :: VectorProp Bool -> VectorProp Bool -> VectorProp Bool -> TerOp -> VectorProp Bool
inferEmptyTerOp _ e2 e3 op =
  case op of
    -- FIXME conjunction holds only for the first component of the output.
    -- the other ones are already empty if their respective input is empty
    CombineVec -> let ue2 = unpack e2
                      ue3 = unpack e3
                  in VPropTriple (ue2 && ue3) ue2 ue3
    
