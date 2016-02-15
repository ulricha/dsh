-- FIXME complete rules

module Database.DSH.VL.Opt.Properties.Card where

import Database.DSH.VL.Lang

import Database.DSH.VL.Opt.Properties.Types
import Database.DSH.VL.Opt.Properties.Common

unp :: Show a => VectorProp a -> Either String a
unp = unpack "Properties.Card"

inferCardOneNullOp :: NullOp -> Either String (VectorProp Bool)
inferCardOneNullOp op =
  case op of
    Lit (_, f, _) -> Right $ VProp $ frameLen f == 1
    TableRef _    -> Right $ VProp False

inferCardOneUnOp :: VectorProp Bool -> UnOp -> Either String (VectorProp Bool)
inferCardOneUnOp c op =
  case op of
    UniqueS -> Right c
    Aggr _ -> Right $ VProp True
    WinFun _ -> Right c
    UnboxKey -> Right c
    Segment -> Right c
    Unsegment -> Right c
    Nest -> unp c >>= (\uc -> return $ VPropPair True uc)
    Project _  -> Right c
    ReverseS -> unp c >>= (\uc -> return $ VPropPair uc uc)
    Select _ -> Right $ VPropPair False False
    SortS _ -> unp c >>= (\uc -> return $ VPropPair uc uc)
    GroupS _ -> unp c >>= (\uc -> return $ VPropTriple uc uc uc)
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
    GroupAggr ([], _) -> Right $ VProp True
    GroupAggr (_, _)  -> Right c
    NumberS -> Right c

inferCardOneBinOp :: VectorProp Bool -> VectorProp Bool -> BinOp -> Either String (VectorProp Bool)
inferCardOneBinOp c1 c2 op =
  case op of
    AggrS _ -> return $ VProp False
    ReplicateNest -> return $ VPropPair False False
    ReplicateScalar -> unp c2 >>= (\uc -> return $ VPropPair uc uc)
    AppKey -> return $ VPropPair False False
    AppSort -> return $ VPropPair False False
    AppFilter -> return $ VPropPair False False
    AppRep -> return $ VPropPair False False
    UnboxSng -> return $ VPropPair False False
    -- FIXME more precisely: empty(left) and card1(right) or card1(left) and empty(right)
    AppendS -> Right $ VPropTriple False False False
    Align -> VProp <$> ((||) <$> unp c1 <*> unp c2)
    CartProductS -> return $ VPropTriple False False False
    NestProductS -> return $ VPropTriple False False False
    ThetaJoinS _ -> return $ VPropTriple False False False
    NestJoinS _ -> return $ VPropTriple False False False
    GroupJoin _ -> return $ VProp False
    SemiJoinS _ -> return $ VPropPair False False
    AntiJoinS _ -> return $ VPropPair False False
    ZipS -> do
      c <- (||) <$> unp c1 <*> unp c2
      return $ VPropTriple c c c

inferCardOneTerOp :: VectorProp Bool -> VectorProp Bool -> VectorProp Bool -> TerOp -> Either String (VectorProp Bool)
inferCardOneTerOp _ _ _ op =
  case op of
    Combine -> return $ VPropTriple False False False
