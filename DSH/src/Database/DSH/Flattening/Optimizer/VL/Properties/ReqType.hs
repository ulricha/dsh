
module Optimizer.VL.Properties.ReqType where

import Data.Maybe

import Database.Algebra.VL.Data
  
import Optimizer.VL.Properties.Types
  
unp :: VectorProp a -> a
unp (VProp x) = x
unp _         = error "foo"
  
updateValueVector :: VectorProp VectorType -> VectorProp VectorType -> VectorProp VectorType
updateValueVector (VProp (ValueVector w)) (VProp (ValueVector w')) = VProp $ ValueVector $ max w w'
updateValueVector (VProp DescrVector)     (VProp (ValueVector w))  = VProp $ ValueVector w
updateValueVector (VProp (ValueVector w)) (VProp DescrVector)      = VProp $ ValueVector w
updateValueVector (VProp DescrVector)     (VProp DescrVector)      = VProp DescrVector

maxProjectCol :: [PayloadProj] -> DBCol
maxProjectCol ps = 
  case mapMaybe onlyCols ps of
    cs@(_ : _) -> maximum cs
    []         -> 0
  where onlyCols (PLConst _) = Nothing
        onlyCols (PLCol c)   = Just c
        
maxInputCol :: Expr1 -> DBCol
maxInputCol (App1 _ e1 e2) = max (maxInputCol e1) (maxInputCol e2)
maxInputCol (Column1 c)    = c
maxInputCol (Constant1 _)  = 0


inferReqTypeUnOp :: VectorProp VectorType 
                    -> VectorProp VectorType 
                    -> VectorProp VectorType
                    -> UnOp 
                    -> VectorProp VectorType
inferReqTypeUnOp ownrt crt ct op = 
  case op of
    ProjectL ps      -> updateValueVector (VProp (ValueVector $ length ps)) crt
    ProjectA ps      -> undefined
    NotPrim          -> VProp $ AtomicVector 1
    NotVec           -> VProp $ ValueVector 1
    LengthA          -> VProp $ DescrVector
    DescToRename     -> VProp $ DescrVector
    ToDescr          -> VProp $ ValueVector 0
    Segment          -> ownrt
    VecSum _         -> VProp $ ValueVector 1
    VecMin           -> VProp $ ValueVector 1
    VecMinL          -> VProp $ ValueVector 1
    VecMax           -> VProp $ ValueVector 1
    VecMaxL          -> VProp $ ValueVector 1
    IntegerToDoubleA -> VProp $ ValueVector 1
    IntegerToDoubleL -> VProp $ ValueVector 1
    ReverseA         -> ownrt
    ReverseL         -> ownrt
    FalsePositions   -> VProp $ ValueVector 1
    ProjectRename _  -> VProp $ ValueVector 0
    ProjectPayload p -> VProp $ ValueVector $ maxProjectCol p
    ProjectAdmin _   -> ownrt
    SelectItem       -> VProp $ ValueVector 1
    Only             -> undefined
    Singleton        -> undefined
    CompExpr1 e      -> VProp $ ValueVector $ maxInputCol e
    SelectPos1 _ _   -> ownrt
    SelectPos1L _ _  -> ownrt
    R1               -> 
      case ct of
        VProp _             -> error "foo"
        VPropPair _ t2      -> VPropPair (unp ownrt) t2
        VPropTriple _ t2 t3 -> VPropTriple (unp ownrt) t2 t3
    R2               -> 
      case ct of
        VProp _             -> error "foo"
        VPropPair t1 _      -> VPropPair t1 (unp ownrt)
        VPropTriple t1 t2 _ -> VPropTriple t1 t2 (unp ownrt)
    R3               -> 
      case ct of
        VProp _             -> error "foo"
        VPropPair _ _       -> error "bar"
        VPropTriple t1 t2 _ -> VPropTriple t1 t2 (unp ownrt)
  
inferReqTypeBinOp :: VectorProp VectorType 
                     -> VectorProp VectorType 
                     -> VectorProp VectorType 
                     -> VectorProp VectorType 
                     -> VectorProp VectorType 
                     -> VectorProp VectorType 
                     -> UnOp 
                     -> (VectorProp VectorType, VectorProp VectorType)
inferReqTypeBinOp ownrt ownt crt1 ct1 crt2 ct2 op = 
  case op of
    GroupBy         -> 
      case ownrt of
        VectorTriple _ t2 _ -> (ct1, t2)
        _                   -> undefined
    SortWith        ->
      case ownrt of
        VectorPair t1 _  -> (ct1, t1)
        _                -> undefined
    LengthSeg       -> (VProp DescrVector, VProp DescrVector)
    DistPrim        -> 
      case ownt of
        VPropPair (ValueVector w) PropVector -> (AtomicVector w, DescrVector)
        _                                      -> error "foo"
    DistDesc        ->
      case ownt of
        VPropPair (ValueVector w) PropVector -> (ValueVector w, DescrVector)
        _                                      -> error "foo"
    DistLift        ->
      case ownt of
        VPropPair (ValueVector w) PropVector -> (ValueVector w, DescrVector)
    PropRename      -> (RenameVector, ownrt)
    PropFilter      ->
      case ownrt of
        (VProp
      
        
    
{-
inferReqTypeBinOp :: VectorType 
                     -> VectorType 
                     -> VectorType 
                     -> VectorType 
                     -> VectorType 
                     -> VectorType 
                     -> UnOp 
                     -> (VectorProp VectorType, VectorProp VectorType, VectorProp VectorType)
inferReqTypeBinOp ownType crt1 ct1 crt2 ct2 op = undefined
-}
