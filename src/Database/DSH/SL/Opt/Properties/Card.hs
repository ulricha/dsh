-- FIXME complete rules

module Database.DSH.SL.Opt.Properties.Card where

import qualified Data.Sequence                         as S

import           Database.DSH.Common.VectorLang
import           Database.DSH.SL.Lang

import           Database.DSH.SL.Opt.Properties.Common
import           Database.DSH.SL.Opt.Properties.Types

unp :: Show a => VectorProp a -> Either String a
unp = unpack "Properties.Card"

inferCardOneNullOp :: NullOp -> Either String (VectorProp Bool)
inferCardOneNullOp op =
  case op of
    Lit (_, ss) ->
        case ss of
            UnitSeg sd -> Right $ VProp $ S.length sd == 1
            Segs _     -> Right $ VProp False
    TableRef _ -> Right $ VProp False

inferCardOneUnOp :: VectorProp Bool -> UnOp r e -> Either String (VectorProp Bool)
inferCardOneUnOp c op =
  case op of
    Unique -> Right c
    WinFun _ -> Right c
    UnboxKey -> Right c
    Segment -> Right c
    Unsegment -> Right c
    Project _  -> Right c
    Reverse -> unp c >>= (\uc -> return $ VPropPair uc uc)
    Select _ -> Right $ VPropPair False False
    Sort _ -> unp c >>= (\uc -> return $ VPropPair uc uc)
    Group _ -> unp c >>= (\uc -> return $ VPropTriple uc uc uc)
    R1 ->
      case c of
        VProp _           -> Left "Properties.Card: not a pair/triple"
        VPropPair b _     -> Right $ VProp b
        VPropTriple b _ _ -> Right $ VProp b
    R2 ->
      case c of
        VProp _           -> Left "Properties.Card: not a pair/triple"
        VPropPair _ b     -> Right $ VProp b
        VPropTriple _ b _ -> Right $ VProp b
    R3 ->
      case c of
        VPropTriple _ _ b -> Right $ VProp b
        _                 -> Left "Properties.Card: not a triple"
    GroupAggr (_, _)      -> Right c
    Number -> Right c
    Fold _ -> return $ VProp False

inferCardOneBinOp :: VectorProp Bool -> VectorProp Bool -> BinOp e -> Either String (VectorProp Bool)
inferCardOneBinOp c1 c2 op =
  case op of
    ReplicateNest -> return $ VPropPair False False
    ReplicateScalar -> unp c2 >>= (\uc -> return $ VPropPair uc uc)
    AppKey -> return $ VPropPair False False
    AppSort -> return $ VPropPair False False
    AppFilter -> return $ VPropPair False False
    AppRep -> return $ VPropPair False False
    UnboxSng -> return $ VPropPair False False
    UnboxDefault _ -> return $ VPropPair False False
    -- FIXME more precisely: empty(left) and card1(right) or card1(left) and empty(right)
    Append -> Right $ VPropTriple False False False
    Align -> VProp <$> ((||) <$> unp c1 <*> unp c2)
    CartProduct -> return $ VPropTriple False False False
    ReplicateVector -> return $ VPropPair False False
    ThetaJoin _ -> return $ VPropTriple False False False
    NestJoin _ -> return $ VPropTriple False False False
    GroupJoin _ -> return $ VProp False
    SemiJoin _ -> return $ VPropPair False False
    AntiJoin _ -> return $ VPropPair False False
    Zip -> do
      c <- (||) <$> unp c1 <*> unp c2
      return $ VPropTriple c c c

inferCardOneTerOp :: VectorProp Bool -> VectorProp Bool -> VectorProp Bool -> TerOp -> Either String (VectorProp Bool)
inferCardOneTerOp _ _ _ op =
  case op of
    Combine -> return $ VPropTriple False False False
