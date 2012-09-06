module Optimizer.VL.Properties.Untainted where

-- Infer if the payload is untainted, that is for every tuple of a
-- ValueVector the column content has not been modified. The property
-- tracks the upstream operators from which on the payload is
-- untainted.

import Data.Functor
import Control.Monad
  
import Database.Algebra.Dag.Common

import Optimizer.VL.Properties.Types
  
import Database.Algebra.VL.Data
  
empty :: Untainted
empty = Just []

na :: Untainted
na = Nothing
     
add :: VectorProp Untainted -> AlgNode -> Untainted
add (VProp (Just nodes)) n = Just (n : nodes)
add _                    _ = error "Untainted.add"

inferUntaintedNullOp :: NullOp -> VectorProp Untainted
inferUntaintedNullOp op =
  case op of
    SingletonDescr              -> VProp empty
    ConstructLiteralTable t _   -> VProp empty
    ConstructLiteralValue t _   -> VProp empty
    TableRef              _ cs _ -> VProp empty
  
inferUntaintedUnOp :: VectorProp Untainted -> AlgNode -> UnOp -> VectorProp Untainted
inferUntaintedUnOp u n op = 
  case op of
    Unique -> VProp $ add u n
    UniqueL -> VProp $ add u n
    NotPrim -> VProp empty
    NotVec -> VProp empty
    LengthA -> VProp empty
    DescToRename -> VProp na
    ToDescr -> VProp na
    Segment -> VProp na
    VecSum _ -> VProp empty
    VecMin -> VProp empty
    VecMinL -> VProp empty
    VecMax -> VProp empty
    VecMaxL -> VProp empty
    ProjectL ps -> VProp empty -- FIXME check for identity projections
    ProjectA ps -> VProp empty -- FIXME check for identity projections
    IntegerToDoubleA -> VProp empty
    IntegerToDoubleL -> VProp empty
    ReverseA -> VPropPair (add u n) na
    ReverseL -> VPropPair (add u n) na
    FalsePositions -> VProp $ add u n
    SelectPos1 _ _ -> VPropPair (add u n) na
    SelectPos1L _ _ -> VPropPair (add u n) na
    R1 -> 
      case u of
        VPropPair s1 _ -> VProp s1
        VPropTriple s1 _ _ -> VProp s1
        _ -> error "Input of R1 is not a tuple"
    R2 -> 
      case u of
        VPropPair _ s2 -> VProp s2
        VPropTriple _ s2 _ -> VProp s2
        _ -> error "Input of R2 is not a tuple"
    R3 -> 
      case u of
        VPropTriple s3 _ _ -> VProp s3
        _ -> error "Input of R3 is not a tuple"
    ProjectRename _ -> VProp na
    ProjectPayload valProjs -> VProp empty -- FIXME check for identity projections
    ProjectAdmin _ -> VProp $ add u n
    SelectExpr _ -> VProp $ add u n
    Only -> undefined
    Singleton -> undefined
    CompExpr1L _ -> VProp empty
  
inferUntaintedBinOp :: VectorProp Untainted -> VectorProp Untainted -> AlgNode -> AlgNode -> BinOp -> VectorProp Untainted
inferUntaintedBinOp _ _ n1 n2 op = 
  case op of
    GroupBy -> VPropTriple na empty na
    SortWith -> VPropPair empty na
    LengthSeg -> VProp empty
    DistPrim -> VPropPair empty na
    DistDesc -> VPropPair empty na
    DistLift -> VPropPair empty na
    PropRename -> VProp empty
    PropFilter -> VPropPair empty na
    PropReorder -> VPropPair empty na
    Append -> VPropTriple empty na na
    RestrictVec -> VPropPair empty na
    CompExpr2 _ -> VProp empty
    CompExpr2L _ -> VProp empty
    VecSumL -> VProp empty
    SelectPos _ -> VPropPair empty na
    SelectPosL _ -> VPropPair empty na
    PairA -> VProp empty
    PairL -> VProp empty
    ZipL -> VPropTriple empty na na
    CartProductFlat -> VProp empty
    ThetaJoinFlat _ -> VProp empty

inferUntaintedTerOp :: VectorProp Untainted 
                       -> VectorProp Untainted 
                       -> VectorProp Untainted 
                       -> AlgNode
                       -> AlgNode
                       -> AlgNode
                       -> TerOp -> VectorProp Untainted
inferUntaintedTerOp _ _ _ _ _ _ op = 
  case op of
    CombineVec -> VPropTriple empty na na
