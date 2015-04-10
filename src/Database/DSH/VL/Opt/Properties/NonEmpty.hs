{-# LANGUAGE TemplateHaskell #-}

{-

FIXME semantics need to be clarified.

For an inner vector (one with multiple segments), True means that all
segments contained in the outer vector will be present. This is
particularly true for the output of a grouping operator.

For a non-segmented vector, it is true if we can (derived from a base
tables non-empty property) statically assert that a vector will not be
empty.

This is all rather unclear. Currently, the main purpose of this
property is to avoid the special treatment of empty segments in
segmented aggregates.

-}

-- | Infer wether a vector is statically known to be not empty. For
-- a flat vector (i.e. a vector with only one segment) t his property
-- is true if we can statically decide that the vector is not
-- empty. For an inner vector, i.e. a vector with multiple segments,
-- it is true if *every* segment is non-empty.
module Database.DSH.VL.Opt.Properties.NonEmpty where

import Control.Monad

import Database.DSH.Common.Lang
import Database.DSH.VL.Lang

import Database.DSH.VL.Opt.Properties.Types
import Database.DSH.VL.Opt.Properties.Common

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
    SingletonDescr            -> Right $ VProp False
    Lit (NonEmpty, _, _)      -> Right $ VProp True
    Lit (PossiblyEmpty, _, _) -> Right $ VProp False
    TableRef (_, schema)      -> return $ VProp $ (tableNonEmpty schema) == NonEmpty

inferNonEmptyUnOp :: VectorProp Bool -> UnOp -> Either String (VectorProp Bool)
inferNonEmptyUnOp e op =
  case op of
    WinFun _        -> Right e
    Unique          -> Right e
    UniqueS         -> Right e
    Aggr _          -> Right $ VProp True
    AggrNonEmpty _  -> Right $ VProp True
    UnboxKey     -> Right e
    Segment         -> Right e
    Unsegment       -> Right e
    Reverse         -> let ue = unp e in liftM2 VPropPair ue ue
    ReverseS        -> let ue = unp e in liftM2 VPropPair ue ue
    Project _       -> Right e
    Select _        -> Right $ VPropPair False False
    Sort _          -> let ue = unp e in liftM2 VPropPair ue ue
    SortS _         -> let ue = unp e in liftM2 VPropPair ue ue
    Group _         -> let ue = unp e in liftM3 VPropTriple ue (return True) ue
    -- If the input is not completely empty (that is, segments exist),
    -- grouping leads to a nested vector in which every inner segment
    -- is not empty.
    GroupS _        -> let ue = unp e in liftM3 VPropTriple ue (return True) ue

    -- FIXME this documents the current implementation behaviour, not
    -- what _should_ happen!
    ReshapeS _ -> let ue = unp e in liftM2 VPropPair ue ue
    Reshape _ -> let ue = unp e in liftM2 VPropPair ue ue
    Transpose -> let ue = unp e in liftM2 VPropPair ue ue

    -- FIXME think about it: what happens if we feed an empty vector into the aggr operator?
    GroupAggr (_, _) -> Right e
    Number -> Right e
    NumberS -> Right e
    AggrNonEmptyS _ -> return $ VProp True

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
    DistLift        -> mapUnp e1 e2 (\ue1 ue2 -> VPropPair (ue1 && ue2) (ue1 && ue2))
    AppKey          -> mapUnp e1 e2 (\ue1 ue2 -> VPropPair (ue1 && ue2) (ue1 && ue2))
    AppFilter       -> mapUnp e1 e2 (\ue1 ue2 -> VPropPair (ue1 && ue2) (ue1 && ue2))
    AppSort         -> mapUnp e1 e2 (\ue1 ue2 -> VPropPair (ue1 && ue2) (ue1 && ue2))
    AppRep          -> mapUnp e1 e2 (\ue1 ue2 -> VPropPair (ue1 && ue2) (ue1 && ue2))
    UnboxNested     -> mapUnp e1 e2 (\ue1 ue2 -> VPropPair (ue1 && ue2) (ue1 && ue2))
    UnboxScalar     -> mapUnp e1 e2 (\ue1 ue2 -> VProp (ue1 && ue2))
    Append          -> mapUnp e1 e2 (\ue1 ue2 -> VPropTriple (ue1 || ue2) ue1 ue2)
    AppendS         -> mapUnp e1 e2 (\ue1 ue2 -> VPropTriple (ue1 || ue2) ue1 ue2)
    AggrS _         -> return $ VProp True
    Zip             -> mapUnp e1 e2 (\ue1 ue2 -> VProp (ue1 && ue2))
    Align           -> mapUnp e1 e2 (\ue1 ue2 -> VProp (ue1 && ue2))
    ZipS            -> mapUnp e1 e2 (\ue1 ue2 -> (\p -> VPropTriple p p p) (ue1 && ue2))
    CartProduct     -> mapUnp e1 e2 (\ue1 ue2 -> (\p -> VPropTriple p p p) (ue1 && ue2))
    CartProductS    -> mapUnp e1 e2 (\ue1 ue2 -> (\p -> VPropTriple p p p) (ue1 && ue2))
    NestProductS    -> mapUnp e1 e2 (\ue1 ue2 -> (\p -> VPropTriple p p p) (ue1 && ue2))
    ThetaJoin _     -> return $ VPropTriple False False False
    NestJoin _      -> return $ VPropTriple False False False
    GroupJoin _     -> return $ VProp False
    NestProduct     -> return $ VPropTriple False False False
    ThetaJoinS _    -> return $ VPropTriple False False False
    NestJoinS _     -> return $ VPropTriple False False False
    SemiJoin _      -> return $ VPropPair False False
    SemiJoinS _     -> return $ VPropPair False False
    AntiJoin _      -> return $ VPropPair False False
    AntiJoinS _     -> return $ VPropPair False False
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

