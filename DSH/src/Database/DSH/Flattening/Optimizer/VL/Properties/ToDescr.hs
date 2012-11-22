module Optimizer.VL.Properties.ToDescr where

import Database.Algebra.VL.Data
  
import Optimizer.VL.Properties.Types
  
unp :: Show a => VectorProp a -> a
unp (VProp x) = x
unp x         = error $ "unp " ++ (show x)
    
maybeSet :: VectorProp (Maybe Bool) -> VectorProp (Maybe Bool)
maybeSet (VProp (Just b)) = VProp $ Just b
maybeSet (VProp Nothing)  = VProp $ Just True
maybeSet _                = error "maybeSet"

inferToDescrUnOp :: VectorProp (Maybe Bool)
                -> VectorProp (Maybe Bool)
                -> UnOp
                -> VectorProp (Maybe Bool)
inferToDescrUnOp ownToDescr childToDescr op = 
  case op of
    ToDescr          -> maybeSet childToDescr

    SelectPos1 _ _   ->
      case ownToDescr of
        VPropPair t1 _ -> VProp t1
        _                    -> error "SelectPos1"

    SelectPos1L _ _   ->
      case ownToDescr of
        VPropPair t1 _ -> VProp t1
        _                        -> error "SelectPos1L"

    R1               -> 
      case childToDescr of
        VProp _              -> error $ "R1 " ++ (show childToDescr)
        VPropPair t1 t2      -> VPropPair (unp (andToDescr (VProp t1) ownToDescr)) t2
        VPropTriple t1 t2 t3 -> VPropTriple (unp (andToDescr (VProp t1) ownToDescr)) t2 t3
    R2               -> 
      case childToDescr of
        VProp _              -> error "R2"
        VPropPair t1 t2      -> VPropPair t1 (unp (andToDescr (VProp t2) ownToDescr))
        VPropTriple t1 t2 t3 -> VPropTriple t1 (unp (andToDescr (VProp t2) ownToDescr)) t3
    R3               -> 
      case childToDescr of
        VProp _              -> error "R3/1"
        VPropPair _ _        -> error "R3/2"
        VPropTriple t1 t2 t3 -> VPropTriple t1 t2 (unp (andToDescr (VProp t3) ownToDescr))
    _                        -> andToDescr ownToDescr childToDescr
  

andToDescr :: VectorProp (Maybe Bool) -> VectorProp (Maybe Bool) -> VectorProp (Maybe Bool)
andToDescr (VProp (Just b1)) (VProp (Just b2)) = VProp $ Just $ b1 && b2
andToDescr (VProp Nothing)   (VProp Nothing)   = VProp Nothing
andToDescr (VProp Nothing)   (VProp (Just b))  = VProp $ Just b
andToDescr (VProp (Just b))  (VProp Nothing)   = VProp $ Just b
andToDescr _                 _                 = error "andToDescr"
                                             
no :: VectorProp (Maybe Bool)
no = VProp $ Just False

yes :: VectorProp (Maybe Bool)
yes = VProp $ Just True

na :: VectorProp (Maybe Bool)
na = VProp Nothing
  
inferToDescrBinOp :: VectorProp (Maybe Bool) 
                 -> VectorProp (Maybe Bool) 
                 -> VectorProp (Maybe Bool)
                 -> BinOp 
                 -> (VectorProp (Maybe Bool), VectorProp (Maybe Bool))
inferToDescrBinOp ownToDescr childToDescr1 childToDescr2 op = 
  case op of
    GroupBy         -> 
      case ownToDescr of
        VPropTriple _ t2 _ -> (no, andToDescr (VProp t2) childToDescr2)
        _                   -> undefined
    SortWith        ->
      case ownToDescr of
        VPropPair t1 _  -> (no, andToDescr (VProp t1) childToDescr2)
        _                -> undefined
    LengthSeg -> (no, no)
    DistPrim -> (na, na)
    DistDesc ->
      case ownToDescr of
        VPropPair t1 _ -> (andToDescr (VProp t1) childToDescr1, na)
        _              -> error "DistDesc"
    DistLift ->
      case ownToDescr of
        VPropPair t1 _ -> (andToDescr (VProp t1) childToDescr1, VProp Nothing)
        _              -> error "DistLift"
    PropRename      -> (na, andToDescr childToDescr2 ownToDescr)
    PropFilter      ->
      case ownToDescr of
        VPropPair t1 _ -> (na, VProp t1)
        _              -> error "PropFilter"
        
    PropReorder ->
      case ownToDescr of
        VPropPair t1 _ -> (na, andToDescr (VProp t1) childToDescr2)
        _              -> error "PropReorder"
        
    Append ->
      case ownToDescr of
        VPropTriple t1 _ _ -> (andToDescr (VProp t1) childToDescr1, andToDescr (VProp t1) childToDescr2)
        _                  -> error "Append"
    RestrictVec ->
      case ownToDescr of
        VPropPair t1 _ -> (andToDescr (VProp t1) childToDescr1, no)
        _              -> error "RestrictVec"
    CompExpr2 _ -> (na, na)
    CompExpr2L _ -> (no, no)
    VecSumL -> (na, no)
    SelectPos _ -> 
      case ownToDescr of
        VPropPair t1 _ -> (andToDescr (VProp t1) childToDescr1, na)
        _              -> error "SelectPos"
    SelectPosL _ -> 
      case ownToDescr of
        VPropPair t1 _ -> (andToDescr (VProp t1) childToDescr1, na)
        _              -> error "SelectPosL"
    PairA -> (na, na)
    PairL -> (andToDescr ownToDescr childToDescr1, andToDescr ownToDescr childToDescr2)
    CartProduct -> (no, no)
    ThetaJoin    _ -> (no, no)
    ZipL -> (andToDescr ownToDescr childToDescr1, andToDescr ownToDescr childToDescr2)
        
inferToDescrTerOp :: VectorProp (Maybe Bool)
                 -> VectorProp (Maybe Bool)
                 -> VectorProp (Maybe Bool)
                 -> VectorProp (Maybe Bool)
                 -> TerOp
                 -> (VectorProp (Maybe Bool), VectorProp (Maybe Bool), VectorProp (Maybe Bool))
inferToDescrTerOp _ _ _ _ _ = (no, no, no)
