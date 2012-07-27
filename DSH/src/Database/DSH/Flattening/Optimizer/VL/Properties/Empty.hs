module Optimizer.VL.Properties.Empty where

import Control.Monad
  
import Database.Algebra.VL.Data
  
import Optimizer.VL.Properties.Types
import Optimizer.VL.Properties.Common
  
unp :: Show a => VectorProp a -> Either String a
unp = unpack "Properties.Empty"
                   
mapUnp :: Show a => VectorProp a
          -> VectorProp a 
          -> (a -> a -> VectorProp a) 
          -> Either String (VectorProp a)
mapUnp = mapUnpack "Properties.Empty"  

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
    ReverseA -> let ue = unp e in liftM2 VPropPair ue ue
    ReverseL -> let ue = unp e in liftM2 VPropPair ue ue
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
      let ue1 = unp e1 
          ue2 = unp e2 
      in liftM3 VPropTriple ue1 (liftM2 (||) ue1 ue2) ue1
    SortWith -> undefined
    LengthSeg -> undefined
    DistPrim -> mapUnp e1 e2 (\ue1 ue2 -> VPropPair (ue1 || ue2) ue2)
    DistDesc -> mapUnp e1 e2 (\ue1 ue2 -> VPropPair (ue1 || ue2) (ue1 || ue2))
    DistLift -> mapUnp e1 e2 (\ue1 ue2 -> VPropPair (ue1 || ue2) (ue1 || ue2))
    PropRename -> mapUnp e1 e2 (\ue1 ue2 -> VProp (ue1 || ue2))
    PropFilter -> mapUnp e1 e2 (\ue1 ue2 -> VPropPair (ue1 || ue2) (ue1 || ue2))
    PropReorder -> mapUnp e1 e2 (\ue1 ue2 -> VPropPair (ue1 || ue2) (ue1 || ue2))
    Append -> mapUnp e1 e2 (\ue1 ue2 -> VPropTriple (ue1 && ue2) ue1 ue2)
    RestrictVec -> mapUnp e1 e2 (\ue1 ue2 -> VPropPair (ue1 || ue2) (ue1 || ue2))
    VecBinOp _ -> mapUnp e1 e2 (\ue1 ue2 -> VProp (ue1 || ue2))
    VecBinOpL _ -> mapUnp e1 e2 (\ue1 ue2 -> VProp (ue1 || ue2))
    VecSumL -> mapUnp e1 e2 (\ue1 ue2 -> VProp $ ue1 && ue2) -- FIXME check if correct
    SelectPos _ -> mapUnp e1 e2 (\ue1 ue2 -> VPropPair (ue1 || ue2) (ue1 || ue2))
    SelectPosL _ -> mapUnp e1 e2 (\ue1 ue2 -> VPropPair (ue1 || ue2) (ue1 || ue2))
    PairA -> mapUnp e1 e2 (\ue1 ue2 -> VProp (ue1 || ue2))
    PairL -> mapUnp e1 e2 (\ue1 ue2 -> VProp (ue1 || ue2))
    ZipL -> mapUnp e1 e2 (\ue1 ue2 -> (\p -> VPropTriple p p p) (ue1 || ue2))
    CartProductFlat -> mapUnp e1 e2 (\ue1 ue2 -> VProp (ue1 || ue2))
    ThetaJoinFlat _ -> mapUnp e1 e2 (\ue1 ue2 -> VProp (ue1 || ue2))
    
inferEmptyTerOp :: VectorProp Bool -> VectorProp Bool -> VectorProp Bool -> TerOp -> Either String (VectorProp Bool)
inferEmptyTerOp _ e2 e3 op =
  case op of
    CombineVec -> let ue2 = unp e2
                      ue3 = unp e3
                  in liftM3 VPropTriple (liftM2 (&&) ue2 ue3) ue2 ue3
    
