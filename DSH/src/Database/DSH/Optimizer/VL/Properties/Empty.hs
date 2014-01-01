module Database.DSH.Optimizer.VL.Properties.Empty where

import Control.Monad
import Control.Applicative
  
import Database.Algebra.VL.Data
  
import Database.DSH.Optimizer.VL.Properties.Types
import Database.DSH.Optimizer.VL.Properties.Common
  
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
    Lit _ []  -> Right $ VProp True
    Lit _ _   -> Right $ VProp False
    TableRef              _ _ _ -> Right $ VProp False
    
inferEmptyUnOp :: VectorProp Bool -> UnOp -> Either String (VectorProp Bool)
inferEmptyUnOp e op =
  case op of
    Unique -> Right e
    UniqueS -> Right e
    Length -> Right $ VProp False
    DescToRename -> Right e
    Segment -> Right e
    Unsegment -> Right e
    Sum _ -> Right $ VProp False
    -- If the input is empty, the avg output will actually be empty
    -- too. However, this is an error case which we would like to avoid
    Avg -> Right $ VProp False
    Min -> Right e
    MinS -> Right e
    Max -> Right e
    MaxS -> Right e
    Reverse -> let ue = unp e in liftM2 VPropPair ue ue
    ReverseS -> let ue = unp e in liftM2 VPropPair ue ue
    FalsePositions -> Right e
    ProjectRename _  -> Right e
    Project _   -> Right e
    Select _       -> Right e
    SortSimple _   -> let ue = unp e in liftM2 VPropPair ue ue
    Only             -> undefined
    Singleton        -> undefined
    SelectPos1 _ _ -> let ue = unp e in liftM2 VPropPair ue ue
    SelectPos1S _ _ -> let ue = unp e in liftM2 VPropPair ue ue
    -- FIXME think about it: what happens if we feed an empty vector into the aggr operator?
    Aggr _ _ -> Right $ VProp False
    Number -> Right e
    NumberS -> Right e
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
    Sort -> do
      ue1 <- unp e1
      ue2 <- unp e2
      let e   = ue1 && ue2
      return $ VPropPair e e

    LengthS -> VProp <$> unp e1
    DistPrim -> mapUnp e1 e2 (\ue1 ue2 -> VPropPair (ue1 || ue2) ue2)
    DistDesc -> mapUnp e1 e2 (\ue1 ue2 -> VPropPair (ue1 || ue2) (ue1 || ue2))
    DistSeg -> mapUnp e1 e2 (\ue1 ue2 -> VPropPair (ue1 || ue2) (ue1 || ue2))
    PropRename -> mapUnp e1 e2 (\ue1 ue2 -> VProp (ue1 || ue2))
    PropFilter -> mapUnp e1 e2 (\ue1 ue2 -> VPropPair (ue1 || ue2) (ue1 || ue2))
    PropReorder -> mapUnp e1 e2 (\ue1 ue2 -> VPropPair (ue1 || ue2) (ue1 || ue2))
    Append -> mapUnp e1 e2 (\ue1 ue2 -> VPropTriple (ue1 && ue2) ue1 ue2)
    Restrict -> mapUnp e1 e2 (\ue1 ue2 -> VPropPair (ue1 || ue2) (ue1 || ue2))
    BinExpr _ -> mapUnp e1 e2 (\ue1 ue2 -> VProp (ue1 || ue2))
    SumS -> mapUnp e1 e2 (\ue1 ue2 -> VProp $ ue1 && ue2) -- FIXME check if correct
    AvgS -> mapUnp e1 e2 (\ue1 ue2 -> VProp $ ue1 && ue2) -- FIXME check if correct
    SelectPos _ -> mapUnp e1 e2 (\ue1 ue2 -> VPropPair (ue1 || ue2) (ue1 || ue2))
    SelectPosS _ -> mapUnp e1 e2 (\ue1 ue2 -> VPropPair (ue1 || ue2) (ue1 || ue2))
    Zip -> mapUnp e1 e2 (\ue1 ue2 -> VProp (ue1 || ue2))
    ZipS -> mapUnp e1 e2 (\ue1 ue2 -> (\p -> VPropTriple p p p) (ue1 || ue2))
    CartProduct -> mapUnp e1 e2 (\ue1 ue2 -> (\p -> VPropTriple p p p) (ue1 || ue2))
    CartProductS -> mapUnp e1 e2 (\ue1 ue2 -> (\p -> VPropTriple p p p) (ue1 || ue2))
    EquiJoin _ _ -> mapUnp e1 e2 (\ue1 ue2 -> (\p -> VPropTriple p p p) (ue1 || ue2))
    EquiJoinS _ _ -> mapUnp e1 e2 (\ue1 ue2 -> (\p -> VPropTriple p p p) (ue1 || ue2))
    SemiJoin _ _ -> mapUnp e1 e2 (\ue1 ue2 -> (\p -> VPropPair p p) (ue1 || ue2))
    SemiJoinS _ _ -> mapUnp e1 e2 (\ue1 ue2 -> (\p -> VPropPair p p) (ue1 || ue2))
    AntiJoin _ _ -> mapUnp e1 e2 (\ue1 _ -> (\p -> VPropPair p p) ue1)
    AntiJoinS _ _ -> mapUnp e1 e2 (\ue1 _ -> (\p -> VPropPair p p) ue1)
    
inferEmptyTerOp :: VectorProp Bool -> VectorProp Bool -> VectorProp Bool -> TerOp -> Either String (VectorProp Bool)
inferEmptyTerOp _ e2 e3 op =
  case op of
    Combine -> let ue2 = unp e2
                   ue3 = unp e3
               in liftM3 VPropTriple (liftM2 (&&) ue2 ue3) ue2 ue3
    
