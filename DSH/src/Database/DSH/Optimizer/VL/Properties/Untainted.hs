module Database.DSH.Optimizer.VL.Properties.Untainted where

-- Infer if the payload is untainted, that is for every tuple of a
-- ValueVector the column content has not been modified. The property
-- tracks the upstream operators from which on the payload is
-- untainted.
   
import Data.Functor

import Database.Algebra.Dag.Common

import Database.DSH.Optimizer.VL.Properties.Types
  
import Database.Algebra.VL.Data
  
empty :: Untainted
empty = Just []

na :: Untainted
na = Nothing
     
add :: VectorProp Untainted -> AlgNode -> Untainted
add (VProp (Just nodes)) n = Just (n : nodes)
add x                    _ = error $ "Untainted.add " ++ (show x)

inferUntaintedNullOp :: NullOp -> VectorProp Untainted
inferUntaintedNullOp op =
  case op of
    SingletonDescr              -> VProp empty
    ConstructLiteralTable _ _   -> VProp empty
    ConstructLiteralValue _ _   -> VProp empty
    TableRef              _ _ _ -> VProp empty
  
inferUntaintedUnOp :: VectorProp Untainted -> AlgNode -> UnOp -> VectorProp Untainted
inferUntaintedUnOp u n op = 
  case op of
    Unique -> VProp $ add u n
    UniqueL -> VProp $ add u n
    NotPrim -> VProp empty
    NotVec -> VProp empty
    LengthA -> VProp empty
    DescToRename -> VProp na
    Segment -> VProp $ add u n
    Unsegment -> VProp $ add u n
    VecSum _ -> VProp empty
    VecAvg -> VProp empty
    VecMin -> VProp empty
    VecMinL -> VProp empty
    VecMax -> VProp empty
    VecMaxL -> VProp empty
    ProjectL _ -> VProp empty -- FIXME check for identity projections
    ProjectA _ -> VProp empty -- FIXME check for identity projections
    IntegerToDoubleA -> VProp empty
    IntegerToDoubleL -> VProp empty
    ReverseA -> VPropPair (add u n) na
    ReverseL -> VPropPair (add u n) na
    FalsePositions -> VProp $ add u n
    SelectPos1 _ _ -> VPropPair (add u n) na
    SelectPos1L _ _ -> VPropPair (add u n) na
    R1 -> 
      case u of
        VPropPair s1 _ -> VProp $ (:) n <$> s1
        VPropTriple s1 _ _ -> VProp $ (:) n <$> s1
        _ -> error "Input of R1 is not a tuple"
    R2 -> 
      case u of
        VPropPair _ s2 -> VProp $ (:) n <$> s2
        VPropTriple _ s2 _ -> VProp $ (:) n <$> s2
        _ -> error "Input of R2 is not a tuple"
    R3 -> 
      case u of
        VPropTriple s3 _ _ -> VProp $ (:) n <$> s3
        _ -> error "Input of R3 is not a tuple"
    ProjectRename _ -> VProp na
    ProjectPayload _ -> VProp empty -- FIXME check for identity projections
    ProjectAdmin _ -> VProp $ add u n
    SelectExpr _ -> VProp $ add u n
    Only -> undefined
    Singleton -> undefined
    CompExpr1L _ -> VProp empty
    VecAggr _ _ -> VProp empty
  
-- FIXME implement
inferUntaintedBinOp :: VectorProp Untainted -> VectorProp Untainted -> AlgNode -> AlgNode -> BinOp -> VectorProp Untainted
inferUntaintedBinOp _ _ _ _ op = 
  case op of
    GroupBy -> VPropTriple empty empty na
    SortWith -> VPropPair empty na
    LengthSeg -> VProp empty
    DistPrim -> VPropPair empty na
    DistDesc -> VPropPair empty na
    DistLift -> VPropPair empty  na
    PropRename -> VProp empty
    PropFilter -> VPropPair empty na
    PropReorder -> VPropPair empty na
    Append -> VPropTriple empty na na
    RestrictVec -> VPropPair empty na
    CompExpr2 _ -> VProp empty
    CompExpr2L _ -> VProp empty
    VecSumL -> VProp empty
    VecAvgL -> VProp empty
    SelectPos _ -> VPropPair empty na
    SelectPosL _ -> VPropPair empty na
    PairA -> VProp empty
    PairL -> VProp empty
    ZipL -> VPropTriple empty na na
    CartProduct  -> VPropTriple empty na na
    CartProductL -> VPropTriple empty na na
    EquiJoin _ _ -> VPropTriple empty na na
    EquiJoinL _ _ -> VPropTriple empty na na

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
