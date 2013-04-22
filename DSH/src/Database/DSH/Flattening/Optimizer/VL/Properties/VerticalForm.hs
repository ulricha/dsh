module Database.DSH.Flattening.Optimizer.VL.Properties.VerticalForm where
       
import Database.Algebra.Dag.Common
import Database.Algebra.VL.Data

import Database.DSH.Flattening.Optimizer.VL.Properties.Common
import Database.DSH.Flattening.Optimizer.VL.Properties.Types

no :: Either String (VectorProp IntactSince)
no = Right $ VProp []

noPair :: Either String (VectorProp IntactSince)
noPair = Right $ VPropPair [] []

noTriple :: Either String (VectorProp IntactSince)
noTriple = Right $ VPropTriple [] [] []

yes :: VectorProp IntactSince -> AlgNode -> Either String (VectorProp IntactSince)
yes (VProp nodes) n = Right $ VProp $ n : nodes
yes _             _ = Left "VerticallyIntact.yes: no single property"

unp :: Show a => VectorProp a -> Either String a
unp = unpack "Properties.Empty"
                   
mapUnp :: Show a => VectorProp a
          -> VectorProp a 
          -> (a -> a -> VectorProp a) 
          -> Either String (VectorProp a)
mapUnp = mapUnpack "Properties.Empty"  

inferVerticallyIntactNullOp :: NullOp -> Either String (VectorProp IntactSince)
inferVerticallyIntactNullOp _ = Right $ VProp []
                      
inferVerticallyIntactUnOp :: VectorProp IntactSince -> AlgNode -> UnOp -> Either String (VectorProp IntactSince)
inferVerticallyIntactUnOp childIntact c op =
  case op of
    Unique -> no
    UniqueL -> no
    NotPrim -> yes childIntact c
    NotVec -> yes childIntact c
    LengthA -> no
    DescToRename -> yes childIntact c
    ToDescr -> yes childIntact c
    Segment -> yes childIntact c
    Unsegment -> yes childIntact c
    VecSum _ -> no
    VecAvg -> no
    VecMin -> no
    VecMinL -> no
    VecMax -> no
    VecMaxL -> no
    ProjectL _ -> yes childIntact c
    ProjectA _ -> yes childIntact c
    IntegerToDoubleA -> yes childIntact c
    IntegerToDoubleL -> yes childIntact c
    ReverseA -> no
    ReverseL -> noPair
    FalsePositions -> no
    ProjectRename _  -> yes childIntact c
    ProjectPayload _   -> yes childIntact c
    ProjectAdmin _   -> yes childIntact c
    SelectExpr _       -> no
    Only             -> yes childIntact c
    Singleton        -> yes childIntact c
    CompExpr1L _ -> yes childIntact c
    SelectPos1 _ _ -> noPair 
    SelectPos1L _ _ -> noPair
    R1 -> 
      case childIntact of
        VProp _           -> Left "Properties.VerticallyIntact: not a pair/triple"
        VPropPair b _     -> Right $ VProp b
        VPropTriple b _ _ -> Right $ VProp b
    R2 ->
      case childIntact of
        VProp _           -> Left "Properties.VerticallyIntact: not a pair/triple"
        VPropPair _ b     -> Right $ VProp b
        VPropTriple _ b _ -> Right $ VProp b
    R3 ->
      case childIntact of
        VPropTriple _ _ b -> Right $ VProp b
        _                 -> Left "Properties.VerticallyIntact: not a triple"
    
inferVerticallyIntactBinOp :: VectorProp IntactSince 
                           -> VectorProp IntactSince 
                           -> AlgNode 
                           -> AlgNode 
                           -> BinOp 
                           -> Either String (VectorProp IntactSince)
inferVerticallyIntactBinOp _ rightChildIntact _ c2 op =
  case op of
    GroupBy -> noTriple
    SortWith -> noPair
    LengthSeg -> no
    DistPrim -> noPair
    DistDesc -> noPair
    DistLift -> noPair
    PropRename -> yes rightChildIntact c2
    PropFilter -> noPair
    PropReorder -> noPair
    Append -> noTriple
    RestrictVec -> noPair
    CompExpr2 _ -> no
    CompExpr2L _ -> no
    VecSumL -> no
    VecAvgL -> no
    SelectPos _ -> noPair
    SelectPosL _ -> noPair
    PairA -> no
    PairL -> no
    ZipL -> noTriple
    CartProduct -> noTriple
    ThetaJoin    _ -> noPair
    
inferVerticallyIntactTerOp :: VectorProp IntactSince 
                           -> VectorProp IntactSince 
                           -> VectorProp IntactSince 
                           -> AlgNode
                           -> AlgNode
                           -> AlgNode
                           -> TerOp 
                           -> Either String (VectorProp IntactSince)
inferVerticallyIntactTerOp _ _ _ _ _ _ op =
  case op of
    CombineVec -> noTriple
    


