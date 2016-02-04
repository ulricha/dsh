{-# LANGUAGE MonadComprehensions #-}

-- | Statically infer information about the segments of a vector. Currently we
-- can determine wether the vector is 'flat' (i.e. has only the unit segment) or
-- whether it is a proper segmented vector.
module Database.DSH.VL.Opt.Properties.Segments where

import Data.List
import Control.Monad.Except

import Database.DSH.VL.Lang
import Database.DSH.Common.Lang

import Database.DSH.VL.Opt.Properties.Types
import Database.DSH.VL.Opt.Properties.Common

unp :: Show a => VectorProp a -> Either String a
unp = unpack "Properties.Segments"

inferSegmentsNullOp :: NullOp -> Either String (VectorProp Segments)
inferSegmentsNullOp op =
  case op of
    -- Check wether all rows are in the unit segment
    Lit (_, rows) -> pure $ VProp $ if all (== IntV 1) $ head $ transpose rows
                                    then UnitSeg
                                    else Segd
    TableRef _    -> pure $ VProp UnitSeg

flatInputs :: Segments -> Segments -> Either String Segments
flatInputs UnitSeg UnitSeg = pure UnitSeg
flatInputs Segd    Segd    = pure Segd
flatInputs NA      _       = throwError "Properties.Segments: unexpected NA input"
flatInputs _       NA      = throwError "Properties.Segments: unexpected NA input"
flatInputs _       _       = throwError "Properties.Segments: inconsistent inputs"

inferSegmentsUnOp :: VectorProp Segments -> UnOp -> Either String (VectorProp Segments)
inferSegmentsUnOp c op =
  case op of
    UniqueS     -> pure c
    Aggr _      -> pure $ VProp UnitSeg
    WinFun _    -> pure c
    UnboxKey    -> pure c
    Segment     -> pure $ VProp Segd
    Unsegment   -> pure $ VProp UnitSeg
    Nest        -> pure $ VPropPair UnitSeg Segd
    Project _   -> pure c
    ReverseS    -> [ VPropPair f NA | f <- unp c ]
    Select _    -> [ VPropPair f NA | f <- unp c ]
    SortS _     -> [ VPropPair f NA | f <- unp c ]
    GroupS _    -> [ VPropTriple f Segd NA | f <- unp c ]
    GroupAggr _ -> pure c
    NumberS     -> pure c
    R1          ->
      case c of
        VProp _           -> throwError "Properties.Card: not a pair/triple"
        VPropPair b _     -> pure $ VProp b
        VPropTriple b _ _ -> pure $ VProp b
    R2          ->
      case c of
        VProp _           -> throwError "Properties.Card: not a pair/triple"
        VPropPair _ b     -> pure $ VProp b
        VPropTriple _ b _ -> pure $ VProp b
    R3          ->
      case c of
        VPropTriple _ _ b -> pure $ VProp b
        _                 -> throwError "Properties.Card: not a triple"

inferSegmentsBinOp :: VectorProp Segments -> VectorProp Segments -> BinOp -> Either String (VectorProp Segments)
inferSegmentsBinOp c1 c2 op =
  case op of
    AggrS _         -> pure $ VProp Segd
    ReplicateNest   -> pure $ VPropPair Segd NA
    ReplicateScalar -> [ VPropPair f NA | f <- unp c2 ]
    AppKey          -> pure $ VPropPair Segd NA
    AppSort         -> pure $ VPropPair Segd NA
    AppFilter       -> pure $ VPropPair Segd NA
    AppRep          -> pure $ VPropPair Segd NA
    UnboxSng        -> [ VPropPair f NA | f <- unp c2 ]
    Append          -> pure $ VPropTriple UnitSeg NA NA
    AppendS         -> join [ VPropTriple <$> flatInputs f1 f2 <*> pure NA <*> pure NA | f1 <- unp c1, f2 <- unp c2 ]
    Align           -> join [ VProp <$> flatInputs f1 f2 | f1 <- unp c1, f2 <- unp c2 ]
    CartProductS    -> join [ VPropTriple <$> flatInputs f1 f2 <*> pure NA <*> pure NA | f1 <- unp c1, f2 <- unp c2 ]
    NestProductS    -> pure $ VPropTriple Segd NA NA
    ThetaJoinS _    -> join [ VPropTriple <$> flatInputs f1 f2 <*> pure NA <*> pure NA | f1 <- unp c1, f2 <- unp c2 ]
    NestJoinS _     -> pure $ VPropTriple Segd NA NA
    GroupJoin _     -> join [ VProp <$> flatInputs f1 f2 | f1 <- unp c1, f2 <- unp c2 ]
    SemiJoinS _     -> join [ VPropPair <$> flatInputs f1 f2 <*> pure NA | f1 <- unp c1, f2 <- unp c2 ]
    AntiJoinS _     -> join [ VPropPair <$> flatInputs f1 f2 <*> pure NA | f1 <- unp c1, f2 <- unp c2 ]
    Zip             -> pure $ VPropTriple UnitSeg NA NA
    ZipS            -> join [ VPropTriple <$> flatInputs f1 f2 <*> pure NA <*> pure NA | f1 <- unp c1, f2 <- unp c2 ]

inferSegmentsTerOp :: VectorProp Segments -> VectorProp Segments -> VectorProp Segments -> TerOp -> Either String (VectorProp Segments)
inferSegmentsTerOp _ _ _ op =
  case op of
    Combine -> pure $ VPropTriple Segd NA NA
