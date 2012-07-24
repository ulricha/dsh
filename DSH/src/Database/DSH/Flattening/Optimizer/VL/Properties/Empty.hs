module Optimizer.VL.Properties.Empty where

import Control.Monad

import Database.Algebra.VL.Data
  
import Optimizer.VL.Properties.Types
  
unpack :: VectorProp Bool -> Either String Bool
unpack (VProp b) = Right b
unpack x         = Left $ "no single vector in Properties.Empty " ++ (show x)
                   
mapUnpack :: VectorProp Bool 
             -> VectorProp Bool 
             -> (Bool -> Bool -> VectorProp Bool) 
             -> Either String (VectorProp Bool)
mapUnpack e1 e2 f = let ue1 = unpack e1
                        ue2 = unpack e2
                    in liftM2 f ue1 ue2
  
inferEmptyNullOp :: NullOp -> Either String (VectorProp Bool)
inferEmptyNullOp op =
  case op of
    SingletonDescr              -> Right $ VProp False
    ConstructLiteralTable _ []  -> Right $ VProp True
    ConstructLiteralTable _ _   -> Right $ VProp False
    ConstructLiteralValue _ []  -> Right $ VProp True
    ConstructLiteralValue _ _   -> Right $ VProp False
    TableRef              _ _ _ -> Right $ VProp False
    
inferEmptyUnOp :: VectorProp Bool -> UnOp -> Either String (VectorProp Bool)
inferEmptyUnOp e op =
  case op of
    Unique -> Right e
    UniqueL -> Right e
    NotPrim -> Right e
    NotVec -> Right e
    LengthA -> Right $ VProp False
    DescToRename -> Right e
    ToDescr -> Right e
    Segment -> Right e
    VecSum _ -> Right $ VProp False
    VecMin -> Right e
    VecMinL -> Right e
    VecMax -> Right e
    VecMaxL -> Right e
    ProjectL _ -> Right e
    ProjectA _ -> Right e
    IntegerToDoubleA -> Right e
    IntegerToDoubleL -> Right e
    ReverseA -> let ue = unpack e in liftM2 VPropPair ue ue
    ReverseL -> let ue = unpack e in liftM2 VPropPair ue ue
    FalsePositions -> Right e
    ProjectRename _  -> Right e
    ProjectValue _   -> Right e
    SelectItem       -> Right e
    Only             -> undefined
    Singleton        -> undefined
    VecBinOpSingle _ -> Right e
    R1 -> 
      case e of
        VProp _           -> Left "Properties.Empty: not a pair/triple"
        VPropPair b _     -> Right $ VProp b
        VPropTriple b _ _ -> Right $ VProp b
    R2 ->
      case e of
        VProp _           -> Left "Properties.Empty: not a pair/triple"
        VPropPair _ b     -> Right $ VProp b
        VPropTriple _ b _ -> Right $ VProp b
    R3 ->
      case e of
        VPropTriple _ _ b -> Right $ VProp b
        _                 -> Left "Properties.Empty: not a triple"
    
inferEmptyBinOp :: VectorProp Bool -> VectorProp Bool -> BinOp -> Either String (VectorProp Bool)
inferEmptyBinOp e1 e2 op =
  case op of
    GroupBy -> 
      let ue1 = unpack e1 
          ue2 = unpack e2 
      in liftM3 VPropTriple ue1 (liftM2 (||) ue1 ue2) ue1
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
    VecBinOp _ -> mapUnpack e1 e2 (\ue1 ue2 -> VProp (ue1 || ue2))
    VecBinOpL _ -> mapUnpack e1 e2 (\ue1 ue2 -> VProp (ue1 || ue2))
    VecSumL -> mapUnpack e1 e2 (\ue1 ue2 -> VProp $ ue1 && ue2) -- FIXME check if correct
    SelectPos _ -> mapUnpack e1 e2 (\ue1 ue2 -> VPropPair (ue1 || ue2) (ue1 || ue2))
    SelectPosL _ -> mapUnpack e1 e2 (\ue1 ue2 -> VPropPair (ue1 || ue2) (ue1 || ue2))
    PairA -> mapUnpack e1 e2 (\ue1 ue2 -> VProp (ue1 || ue2))
    PairL -> mapUnpack e1 e2 (\ue1 ue2 -> VProp (ue1 || ue2))
    ZipL -> mapUnpack e1 e2 (\ue1 ue2 -> (\p -> VPropTriple p p p) (ue1 || ue2))
    CartProduct -> mapUnpack e1 e2 (\ue1 ue2 -> VProp (ue1 || ue2))
    ThetaJoin _ -> mapUnpack e1 e2 (\ue1 ue2 -> VProp (ue1 || ue2))
    
inferEmptyTerOp :: VectorProp Bool -> VectorProp Bool -> VectorProp Bool -> TerOp -> Either String (VectorProp Bool)
inferEmptyTerOp _ e2 e3 op =
  case op of
    CombineVec -> let ue2 = unpack e2
                      ue3 = unpack e3
                  in liftM3 VPropTriple (liftM2 (&&) ue2 ue3) ue2 ue3
    
