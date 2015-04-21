{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.VL.Opt.Properties.Empty where

import Control.Monad

import Database.DSH.VL.Lang

import Database.DSH.VL.Opt.Properties.Types
import Database.DSH.VL.Opt.Properties.Common

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
    Lit (_, _, []) -> Right $ VProp True
    Lit{}          -> Right $ VProp False
    TableRef{}     -> Right $ VProp False

inferEmptyUnOp :: VectorProp Bool -> UnOp -> Either String (VectorProp Bool)
inferEmptyUnOp e op =
  case op of
    Nest             -> VPropPair False <$> unp e
    WinFun _         -> Right e
    Unique           -> Right e
    UniqueS          -> Right e
    Aggr _           -> Right $ VProp False
    UnboxKey         -> Right e
    Segment          -> let ue = unp e in liftM2 VPropPair ue ue
    Reverse          -> let ue = unp e in liftM2 VPropPair ue ue
    ReverseS         -> let ue = unp e in liftM2 VPropPair ue ue
    Project _        -> Right e
    Select _         -> let ue = unp e in liftM2 VPropPair ue ue
    Sort _           -> let ue = unp e in liftM2 VPropPair ue ue
    SortS _          -> let ue = unp e in liftM2 VPropPair ue ue
    Group _          -> let ue = unp e in liftM3 VPropTriple ue ue ue
    GroupS _         -> let ue = unp e in liftM3 VPropTriple ue ue ue

    -- FIXME this documents the current implementation behaviour, not
    -- what _should_ happen!
    ReshapeS _       -> let ue = unp e in liftM2 VPropPair ue ue
    Reshape _        -> let ue = unp e in liftM2 VPropPair ue ue
    Transpose        -> let ue = unp e in liftM2 VPropPair ue ue

    -- FIXME think about it: what happens if we feed an empty vector into the aggr operator?
    GroupAggr (_, _) -> Right $ VProp False
    Number           -> Right e
    NumberS          -> Right e

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
        p                 -> Left ("Properties.Empty: not a triple" ++ show p)


inferEmptyBinOp :: VectorProp Bool -> VectorProp Bool -> BinOp -> Either String (VectorProp Bool)
inferEmptyBinOp e1 e2 op =
  case op of
    DistLift -> mapUnp e1 e2 (\ue1 ue2 -> VPropPair (ue1 || ue2) (ue1 || ue2))
    -- PropRename -> mapUnp e1 e2 (\ue1 ue2 -> VProp (ue1 || ue2))
    -- PropFilter -> mapUnp e1 e2 (\ue1 ue2 -> VPropPair (ue1 || ue2) (ue1 || ue2))
    -- PropReorder -> mapUnp e1 e2 (\ue1 ue2 -> VPropPair (ue1 || ue2) (ue1 || ue2))
    UnboxScalar -> mapUnp e1 e2 (\ue1 ue2 -> VProp (ue1 || ue2))
    Append -> mapUnp e1 e2 (\ue1 ue2 -> VPropTriple (ue1 && ue2) ue1 ue2)
    AppendS -> mapUnp e1 e2 (\ue1 ue2 -> VPropTriple (ue1 && ue2) ue1 ue2)
    AggrS _ -> return $ VProp False
    Zip -> mapUnp e1 e2 (\ue1 ue2 -> let p = ue1 || ue2 in VPropTriple p p p)
    Align -> mapUnp e1 e2 (\ue1 ue2 -> VProp (ue1 || ue2))
    ZipS -> mapUnp e1 e2 (\ue1 ue2 -> (\p -> VPropTriple p p p) (ue1 || ue2))
    CartProduct -> mapUnp e1 e2 (\ue1 ue2 -> (\p -> VPropTriple p p p) (ue1 || ue2))
    CartProductS -> mapUnp e1 e2 (\ue1 ue2 -> (\p -> VPropTriple p p p) (ue1 || ue2))
    NestProductS -> mapUnp e1 e2 (\ue1 ue2 -> (\p -> VPropTriple p p p) (ue1 || ue2))
    ThetaJoin _ -> mapUnp e1 e2 (\ue1 ue2 -> (\p -> VPropTriple p p p) (ue1 || ue2))
    NestJoin _ -> mapUnp e1 e2 (\ue1 ue2 -> (\p -> VPropTriple p p p) (ue1 || ue2))
    GroupJoin _ -> mapUnp e1 e2 (\ue1 ue2 -> VProp (ue1 || ue2))
    NestProduct -> mapUnp e1 e2 (\ue1 ue2 -> (\p -> VPropTriple p p p) (ue1 || ue2))
    ThetaJoinS _ -> mapUnp e1 e2 (\ue1 ue2 -> (\p -> VPropTriple p p p) (ue1 || ue2))
    NestJoinS _ -> mapUnp e1 e2 (\ue1 ue2 -> (\p -> VPropTriple p p p) (ue1 || ue2))
    SemiJoin _ -> mapUnp e1 e2 (\ue1 ue2 -> (\p -> VPropPair p p) (ue1 || ue2))
    SemiJoinS _ -> mapUnp e1 e2 (\ue1 ue2 -> (\p -> VPropPair p p) (ue1 || ue2))
    AntiJoin _ -> mapUnp e1 e2 (\ue1 _ -> (\p -> VPropPair p p) ue1)
    AntiJoinS _ -> mapUnp e1 e2 (\ue1 _ -> (\p -> VPropPair p p) ue1)
    AppKey -> mapUnp e1 e2 (\ue1 ue2 -> (\p -> VPropPair p p) (ue1 || ue2))
    AppFilter -> mapUnp e1 e2 (\ue1 ue2 -> (\p -> VPropPair p p) (ue1 || ue2))
    AppSort -> mapUnp e1 e2 (\ue1 ue2 -> (\p -> VPropPair p p) (ue1 || ue2))
    AppRep -> mapUnp e1 e2 (\ue1 ue2 -> (\p -> VPropPair p p) (ue1 || ue2))
    -- FIXME This documents the current behaviour of the algebraic
    -- implementations, not what _should_ happen!
    TransposeS -> mapUnp e1 e2 (\ue1 ue2 -> (\p -> VPropPair p p) (ue1 || ue2))

inferEmptyTerOp :: VectorProp Bool -> VectorProp Bool -> VectorProp Bool -> TerOp -> Either String (VectorProp Bool)
inferEmptyTerOp _ e2 e3 op =
  case op of
    Combine -> let ue2 = unp e2
                   ue3 = unp e3
               in liftM3 VPropTriple (liftM2 (&&) ue2 ue3) ue2 ue3

