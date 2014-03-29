{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Optimizer.VL.Properties.NonEmpty where

import Control.Monad
  
import Database.DSH.Common.Lang(nonEmptyHint, Emptiness(..))
import Database.DSH.VL.Lang

import Database.DSH.Optimizer.VL.Properties.Types
import Database.DSH.Optimizer.VL.Properties.Common
  
unp :: Show a => VectorProp a -> Either String a
unp = unpack "Properties.NonEmpty"
                   
mapUnp :: Show a => VectorProp a
          -> VectorProp a 
          -> (a -> a -> VectorProp a) 
          -> Either String (VectorProp a)
mapUnp = mapUnpack "Properties.NonEmpty"  

inferNonEmptyNullOp :: NullOp -> Either String (VectorProp Bool)
inferNonEmptyNullOp op =
  case op of
    SingletonDescr        -> Right $ VProp False
    Lit NonEmpty _ _      -> Right $ VProp True
    Lit PossiblyEmpty _ _ -> Right $ VProp False
    TableRef _ _ hs       -> return $ VProp $ (nonEmptyHint hs) == NonEmpty
    
inferNonEmptyUnOp :: VectorProp Bool -> UnOp -> Either String (VectorProp Bool)
inferNonEmptyUnOp e op =
  case op of
    UniqueS         -> Right e
    Aggr _          -> Right $ VProp True
    AggrNonEmpty _  -> Right $ VProp True
    DescToRename    -> Right e
    Segment         -> Right e
    Unsegment       -> Right e
    Reverse         -> let ue = unp e in liftM2 VPropPair ue ue
    ReverseS        -> let ue = unp e in liftM2 VPropPair ue ue
    Project _       -> Right e
    Select _        -> Right $ VProp False
    SortSimple _    -> let ue = unp e in liftM2 VPropPair ue ue
    GroupSimple _   -> let ue = unp e in liftM2 VPropPair ue ue

    -- FIXME this documents the current implementation behaviour, not
    -- what _should_ happen!
    ReshapeS _ -> let ue = unp e in liftM2 VPropPair ue ue
    Reshape _ -> let ue = unp e in liftM2 VPropPair ue ue
    Transpose -> let ue = unp e in liftM2 VPropPair ue ue

    SelectPos1 _ _ -> return $ VPropPair False False
    SelectPos1S _ _ -> return $ VPropPair False False
    -- FIXME think about it: what happens if we feed an empty vector into the aggr operator?
    GroupAggr _ _ -> Right e
    Number -> Right e
    NumberS -> Right e
  
    R1 -> 
      case e of
        VProp _           -> Left "Properties.NonEmpty: not a pair/triple"
        VPropPair b _     -> Right $ VProp b
        VPropTriple b _ _ -> Right $ VProp b
    R2 ->
      case e of
        VProp _           -> Left "Properties.NonEmpty: not a pair/triple"
        VPropPair _ b     -> Right $ VProp b
        VPropTriple _ b _ -> Right $ VProp b
    R3 ->
      case e of
        VPropTriple _ _ b -> Right $ VProp b
        _                 -> Left "Properties.NonEmpty: not a triple"

    
inferNonEmptyBinOp :: VectorProp Bool -> VectorProp Bool -> BinOp -> Either String (VectorProp Bool)
inferNonEmptyBinOp e1 e2 op =
  case op of
    GroupBy -> do
      ue1 <- unp e1 
      return $ VPropTriple ue1 ue1 ue1
    Sort -> do
      ue1 <- unp e1
      ue2 <- unp e2
      let e   = ue1 && ue2
      return $ VPropPair e e

    DistPrim        -> mapUnp e1 e2 (\ue1 ue2 -> VPropPair (ue1 && ue2) ue2)
    DistDesc        -> mapUnp e1 e2 (\ue1 ue2 -> VPropPair (ue1 && ue2) (ue1 && ue2))
    Align           -> mapUnp e1 e2 (\ue1 ue2 -> VPropPair (ue1 && ue2) (ue1 && ue2))
    PropRename      -> mapUnp e1 e2 (\ue1 ue2 -> VProp (ue1 && ue2))
    PropFilter      -> mapUnp e1 e2 (\ue1 ue2 -> VPropPair (ue1 && ue2) (ue1 && ue2))
    PropReorder     -> mapUnp e1 e2 (\ue1 ue2 -> VPropPair (ue1 && ue2) (ue1 && ue2))
    Append          -> mapUnp e1 e2 (\ue1 ue2 -> VPropTriple (ue1 || ue2) ue1 ue2)
    Restrict        -> return $ VPropPair False False
    BinExpr _       -> mapUnp e1 e2 (\ue1 ue2 -> VProp (ue1 && ue2))
    AggrS _         -> return $ VProp True
    AggrNonEmptyS _ -> return $ VProp True
    SelectPos _     -> mapUnp e1 e2 (\ue1 ue2 -> VPropPair (ue1 || ue2) (ue1 || ue2))
    SelectPosS _    -> mapUnp e1 e2 (\ue1 ue2 -> VPropPair (ue1 || ue2) (ue1 || ue2))
    Zip             -> mapUnp e1 e2 (\ue1 ue2 -> VProp (ue1 && ue2))
    ZipS            -> mapUnp e1 e2 (\ue1 ue2 -> (\p -> VPropTriple p p p) (ue1 && ue2))
    CartProduct     -> mapUnp e1 e2 (\ue1 ue2 -> (\p -> VPropTriple p p p) (ue1 && ue2))
    CartProductS    -> mapUnp e1 e2 (\ue1 ue2 -> (\p -> VPropTriple p p p) (ue1 && ue2))
    NestProductS    -> mapUnp e1 e2 (\ue1 ue2 -> (\p -> VPropTriple p p p) (ue1 && ue2))
    EquiJoin _ _    -> return $ VPropTriple False False False
    EquiJoinS _ _   -> return $ VPropTriple False False False
    NestJoinS _ _   -> return $ VPropTriple False False False
    SemiJoin _ _    -> return $ VPropPair False False
    SemiJoinS _ _   -> return $ VPropPair False False
    AntiJoin _ _    -> return $ VPropPair False False
    AntiJoinS _ _   -> return $ VPropPair False False
    -- FIXME This documents the current behaviour of the algebraic
    -- implementations, not what _should_ happen!
    TransposeS      -> mapUnp e1 e2 (\ue1 ue2 -> (\p -> VPropPair p p) (ue1 || ue2))
    
inferNonEmptyTerOp :: VectorProp Bool -> VectorProp Bool -> VectorProp Bool -> TerOp -> Either String (VectorProp Bool)
inferNonEmptyTerOp e1 e2 e3 op =
  case op of
    Combine -> do
        ue1 <- unp e1
        ue2 <- unp e2
        ue3 <- unp e3
        return $ VPropTriple ue1 ue2 ue3
    
