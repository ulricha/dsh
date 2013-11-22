module Database.DSH.Optimizer.VL.Properties.Const where

import           Data.List

import           Database.Algebra.VL.Data
import           Database.DSH.Optimizer.VL.Properties.Common
import           Database.DSH.Optimizer.VL.Properties.Types

unp :: Show a => VectorProp a -> Either String a
unp = unpack "Properties.Const"

mapUnp :: Show a => VectorProp a
          -> VectorProp a
          -> (a -> a -> VectorProp a)
          -> Either String (VectorProp a)
mapUnp = mapUnpack "Properties.Empty"

fromDBV :: ConstVec -> Either String (ConstDescr, [ConstPayload])
fromDBV (DBVConst d ps)   = Right (d, ps)
fromDBV x                 = Left $ "Properties.Const fromDBV " ++ (show x)

fromDBP :: ConstVec -> Either String [ConstPayload]
fromDBP (DBPConst ps) = Right ps
fromDBP _             = Left "Properties.Const fromDBP"

fromRenameVec :: ConstVec -> Either String (SourceConstDescr, TargetConstDescr)
fromRenameVec (RenameVecConst s t) = Right (s, t)
fromRenameVec x                    = Left ("Properties.Const fromRenameVec " ++ (show x))

fromPropVec :: ConstVec -> Either String (SourceConstDescr, TargetConstDescr)
fromPropVec (PropVecConst s t)  = Right (s, t)
fromPropVec _                   = Left "Properties.Const fromPropVec"


inferConstVecNullOp :: NullOp -> Either String (VectorProp ConstVec)
inferConstVecNullOp op =
  case op of
    SingletonDescr                    -> return $ VProp $ DBVConst (ConstDescr $ N 1) []
    -- do not include the first two columns in the payload columns because they represent descr and pos.
    ConstructLiteralTable colTypes rows      ->
      if null rows
      then return $ VProp $ DBVConst NonConstDescr $ map (const NonConstPL) colTypes
      else return $ VProp $ DBVConst (ConstDescr $ N 1) constCols
        where constCols       = map toConstPayload $ drop 2 $ transpose rows

              toConstPayload col@(c : _) = if all (c ==) col
                                           then ConstPL c
                                           else NonConstPL
              toConstPayload []          = NonConstPL

    ConstructLiteralValue colTypes vals      ->
      if null vals
      then return $ VProp $ DBPConst $ map (const NonConstPL) colTypes
      else return $ VProp $ DBPConst $ map ConstPL $ drop 2 vals
    TableRef              _ cols _    -> return $ VProp $ DBVConst (ConstDescr $ N 1) $ map (const NonConstPL) cols

inferConstVecUnOp :: (VectorProp ConstVec) -> UnOp -> Either String (VectorProp ConstVec)
inferConstVecUnOp c op =
  case op of
    Unique -> return c

    UniqueL -> return c

    NotPrim -> return c

    NotVec -> return c

    LengthA -> do
      return $ VProp $ DBPConst [NonConstPL]

    DescToRename -> do
      (d, _) <- unp c >>= fromDBV
      return $ VProp $ RenameVecConst (SC NonConstDescr) (TC d)

    Segment -> do
      (_, constCols) <- unp c >>= fromDBV
      return $ VProp $ DBVConst NonConstDescr constCols

    Unsegment -> do
      (_, constCols) <- unp c >>= fromDBV
      return $ VProp $ DBVConst NonConstDescr constCols

    VecSum _ -> return $ VProp $ DBVConst (ConstDescr $ N 1) [NonConstPL]
    
    VecAvg -> return c

    VecMin -> return c

    VecMinL -> return c

    VecMax -> return c

    VecMaxL -> return c

    SelectPos1 _ _ -> do
      (d, cols) <- unp c >>= fromDBV
      return $ VPropPair (DBVConst d cols) (PropVecConst (SC NonConstDescr) (TC NonConstDescr))

    SelectPos1L _ _ -> do
      (d, cols) <- unp c >>= fromDBV
      return $ VPropPair (DBVConst d cols) (PropVecConst (SC NonConstDescr) (TC NonConstDescr))

    ProjectL ps -> do
      (d, cols) <- unp c >>= fromDBV
      let cols' = map (\p -> cols !! (p - 1)) ps
      return $ VProp $ DBVConst d cols'

    ProjectA ps -> do
      cols <- unp c >>= fromDBP
      let cols' = map (\p -> cols !! (p - 1)) ps
      return $ VProp $ DBPConst cols'

    IntegerToDoubleA -> return c

    IntegerToDoubleL -> return c

    ReverseA -> do
      (d, cs) <- unp c >>= fromDBV
      return $ VPropPair (DBVConst d cs) (PropVecConst (SC NonConstDescr) (TC NonConstDescr))

    ReverseL -> do
      (d, cs) <- unp c >>= fromDBV
      return $ VPropPair (DBVConst d cs) (PropVecConst (SC NonConstDescr) (TC NonConstDescr))

    FalsePositions -> do
      (d, _) <- unp c >>= fromDBV
      return $ VProp $ DBVConst d [NonConstPL]

    ProjectRename (targetIS, _)  -> do
      -- FIXME this is not precise -- take care of of the source space.
      (d, _) <- unp c >>= fromDBV
      let d' = case targetIS of
            STDescrCol -> d
            STPosCol -> NonConstDescr
            STNumber -> NonConstDescr
      return $ VProp $ RenameVecConst (SC NonConstDescr) (TC d')

    ProjectPayload vps   -> do
      (constDescr, constCols) <- unp c >>= fromDBV

      let constProj (PLConst v)  = ConstPL v
          constProj (PLCol i)    = constCols !! (i - 1)

      return $ VProp $ DBVConst constDescr $ map constProj vps

    ProjectAdmin (dp, _)   -> do
      (constDescr, constCols) <- unp c >>= fromDBV
      let constDescr' = case dp of
            DescrConst n  -> ConstDescr n
            DescrIdentity -> constDescr
            DescrPosCol   -> NonConstDescr

      return $ VProp $ DBVConst constDescr' constCols

    SelectExpr _       -> do
      (d, cols) <- unp c >>= fromDBV
      return $ VProp $ DBVConst d cols

    Only             -> undefined
    Singleton        -> undefined

    CompExpr1L _ -> do
      (d, _) <- unp c >>= fromDBV
      -- FIXME This is not precise: implement constant folding
      return $ VProp $ DBVConst d [NonConstPL]
      
    VecAggr g as -> do
      (d, _) <- unp c >>= fromDBV
      return $ VProp $ DBVConst d (map (const NonConstPL) [ 1 .. (length g) + (length as) ])
      
    Number -> do
      (d, _) <- unp c >>= fromDBV
      return $ VProp $ DBVConst d [NonConstPL]

    NumberL -> do
      (d, _) <- unp c >>= fromDBV
      return $ VProp $ DBVConst d [NonConstPL]

    R1 ->
      case c of
        VProp _           -> Left "Properties.Const: not a pair/triple"
        VPropPair b _     -> Right $ VProp b
        VPropTriple b _ _ -> Right $ VProp b
    R2 ->
      case c of
        VProp _           -> Left "Properties.Const: not a pair/triple"
        VPropPair _ b     -> Right $ VProp b
        VPropTriple _ b _ -> Right $ VProp b
    R3 ->
      case c of
        VPropTriple _ _ b -> Right $ VProp b
        _                 -> Left "Properties.Const: not a triple"

inferConstVecBinOp :: (VectorProp ConstVec) -> (VectorProp ConstVec) -> BinOp -> Either String (VectorProp ConstVec)
inferConstVecBinOp c1 c2 op =
  case op of
    GroupBy -> do
      -- FIXME handle the special case of constant payload columns in the right input (qe)
      (dq, _) <- unp c1 >>= fromDBV
      (_, cols2) <- unp c2 >>= fromDBV
      return $ VPropTriple (DBVConst dq []) (DBVConst NonConstDescr cols2) (PropVecConst (SC NonConstDescr) (TC NonConstDescr))

    SortWith -> do
      (d, cols) <- unp c2 >>= fromDBV
      return $ VPropPair  (DBVConst d cols) (PropVecConst (SC NonConstDescr) (TC NonConstDescr))

    -- FIXME use cardinality property to infer the length if possible
    LengthSeg -> do
      return $ VProp $ DBVConst NonConstDescr [NonConstPL]

    DistPrim -> do
      (d, _) <- unp c2 >>= fromDBV
      cols <- unp c1 >>= fromDBP
      return $ VPropPair (DBVConst d cols) (PropVecConst (SC NonConstDescr) (TC NonConstDescr))

    DistDesc -> do
      (_, cols) <- unp c1 >>= fromDBV
      return $ VPropPair (DBVConst NonConstDescr cols) (PropVecConst (SC NonConstDescr) (TC NonConstDescr))

    DistLift -> do
      (d, _) <- unp c2 >>= fromDBV
      (_, cols) <- unp c1 >>= fromDBV
      return $ VPropPair (DBVConst d cols) (PropVecConst (SC NonConstDescr) (TC NonConstDescr))

    PropRename -> do
      (_, cols) <- unp c2 >>= fromDBV
      (SC _, TC target) <- unp c1 >>= fromRenameVec

      return $ VProp $ DBVConst target cols

    PropFilter -> do
      (_, cols) <- unp c2 >>= fromDBV
      (SC _, TC target) <- unp c1 >>= fromRenameVec

      return $ VPropPair (DBVConst target cols) (RenameVecConst (SC NonConstDescr) (TC NonConstDescr))

    PropReorder -> do
      (_, cols) <- unp c2 >>= fromDBV
      (SC _, TC target) <- unp c1 >>= fromPropVec

      return $ VPropPair (DBVConst target cols) (PropVecConst (SC NonConstDescr) (TC NonConstDescr))

    Append -> do
      (d1, cols1) <- unp c1 >>= fromDBV
      (d2, cols2) <- unp c2 >>= fromDBV

      let constCols = map sameConst $ zip cols1 cols2

          sameConst ((ConstPL v1), (ConstPL v2)) | v1 == v2 = ConstPL v1
          sameConst (_, _)                                  = NonConstPL

          d = case (d1, d2) of
            (ConstDescr n1, ConstDescr n2) | n1 == n2 -> ConstDescr n1
            _                                         -> NonConstDescr

          propVecs = RenameVecConst (SC NonConstDescr) (TC NonConstDescr)

      return $ VPropTriple (DBVConst d constCols) propVecs propVecs

    RestrictVec -> do
      (d, cols) <- unp c1 >>= fromDBV
      return $ VPropPair (DBVConst d cols) (RenameVecConst (SC NonConstDescr) (TC NonConstDescr))

    -- FIXME implement constant folding
    CompExpr2 _ -> do
      return $ VProp $ DBPConst [NonConstPL]

    CompExpr2L _ -> do
      (d1, _) <- unp c1 >>= fromDBV
      (_, _) <- unp c2 >>= fromDBV

      return $ VProp $ DBVConst d1 [NonConstPL]

    -- FIXME handle special cases: empty input, cardinality 1 and const input, ...
    VecSumL -> return $ VProp $ DBVConst NonConstDescr [NonConstPL]
    VecAvgL -> return $ VProp $ DBVConst NonConstDescr [NonConstPL]

    SelectPos _ -> do
      (d1, cols1) <- unp c1 >>= fromDBV

      return $ VPropPair (DBVConst d1 cols1) (RenameVecConst (SC NonConstDescr) (TC NonConstDescr))

    SelectPosL _ -> do
      (d1, cols1) <- unp c1 >>= fromDBV

      return $ VPropPair (DBVConst d1 cols1) (RenameVecConst (SC NonConstDescr) (TC NonConstDescr))

    PairA -> do
      cols1 <- unp c1 >>= fromDBP
      cols2 <- unp c2 >>= fromDBP

      let cols = cols1 ++ cols2

      return $ VProp $ DBPConst cols

    PairL -> do
      (d1, cols1) <- unp c1 >>= fromDBV
      (_, cols2)  <- unp c2 >>= fromDBV

      let cols = cols1 ++ cols2

      return $ VProp $ DBVConst d1 cols

    ZipL -> do
      (d1, cols1) <- unp c1 >>= fromDBV
      (_, cols2)  <- unp c2 >>= fromDBV

      let cols = cols1 ++ cols2
          renameVec = RenameVecConst (SC NonConstDescr) (TC NonConstDescr)

      return $ VPropTriple (DBVConst d1 cols) renameVec renameVec

    CartProduct -> do
      (_, cols1) <- unp c1 >>= fromDBV
      (_, cols2) <- unp c2 >>= fromDBV

      let constCols = cols1 ++ cols2

      -- FIXME check propVec components for correctness/preciseness
      let propVec = PropVecConst (SC NonConstDescr) (TC NonConstDescr)

      -- FIXME descr = 1 is almost certainly not correct
      return $ VPropTriple (DBVConst (ConstDescr $ N 1) constCols) propVec propVec

    CartProductL -> do
      (_, cols1) <- unp c1 >>= fromDBV
      (_, cols2) <- unp c2 >>= fromDBV

      let constCols = cols1 ++ cols2

      -- FIXME check propVec components for correctness/preciseness
      let propVec = PropVecConst (SC NonConstDescr) (TC NonConstDescr)

      -- FIXME descr = 1 is almost certainly not correct
      return $ VPropTriple (DBVConst (ConstDescr $ N 1) constCols) propVec propVec

    EquiJoin _ _ -> do
      (_, cols1) <- unp c1 >>= fromDBV
      (_, cols2) <- unp c2 >>= fromDBV

      let constCols = cols1 ++ cols2

      -- FIXME check propVec components for correctness/preciseness
      let propVec = PropVecConst (SC NonConstDescr) (TC NonConstDescr)

      -- FIXME descr = 1 is almost certainly not correct
      return $ VPropTriple (DBVConst (ConstDescr $ N 1) constCols) propVec propVec

    EquiJoinL _ _ -> do
      (_, cols1) <- unp c1 >>= fromDBV
      (_, cols2) <- unp c2 >>= fromDBV

      let constCols = cols1 ++ cols2

      -- FIXME check propVec components for correctness/preciseness
      let propVec = PropVecConst (SC NonConstDescr) (TC NonConstDescr)

      -- FIXME descr = 1 is almost certainly not correct
      return $ VPropTriple (DBVConst (ConstDescr $ N 1) constCols) propVec propVec
      
    SemiJoin _ _ -> do
      (_, cols1) <- unp c1 >>= fromDBV
      
      -- FIXME This is propably too pessimistic for the source descriptor
      let renameVec = RenameVecConst (SC NonConstDescr) (TC NonConstDescr)

      -- FIXME This is propably too pessimistic for the descr 
      return $ VPropPair (DBVConst NonConstDescr cols1) renameVec

    SemiJoinL _ _ -> do
      (_, cols1) <- unp c1 >>= fromDBV
      
      -- FIXME This is propably too pessimistic for the source descriptor
      let renameVec = RenameVecConst (SC NonConstDescr) (TC NonConstDescr)
  
      -- FIXME This is propably too pessimistic for the descr 
      return $ VPropPair (DBVConst NonConstDescr cols1) renameVec

    AntiJoin _ _ -> do
      (_, cols1) <- unp c1 >>= fromDBV
      
      -- FIXME This is propably too pessimistic for the source descriptor
      let renameVec = RenameVecConst (SC NonConstDescr) (TC NonConstDescr)

      -- FIXME This is propably too pessimistic for the descr 
      return $ VPropPair (DBVConst NonConstDescr cols1) renameVec

    AntiJoinL _ _ -> do
      (_, cols1) <- unp c1 >>= fromDBV
      
      -- FIXME This is propably too pessimistic for the source descriptor
      let renameVec = RenameVecConst (SC NonConstDescr) (TC NonConstDescr)
  
      -- FIXME This is propably too pessimistic for the descr 
      return $ VPropPair (DBVConst NonConstDescr cols1) renameVec

inferConstVecTerOp :: (VectorProp ConstVec) -> (VectorProp ConstVec) -> (VectorProp ConstVec) -> TerOp -> Either String (VectorProp ConstVec)
inferConstVecTerOp c1 c2 c3 op =
  case op of
    CombineVec -> do
      (d1, _) <- unp c1 >>= fromDBV
      (_, cols2)  <- unp c2 >>= fromDBV
      (_, cols3)  <- unp c3 >>= fromDBV

      let constCols = map sameConst $ zip cols2 cols3

          sameConst ((ConstPL v1), (ConstPL v2)) | v1 == v2 = ConstPL v1
          sameConst (_, _)                                  = NonConstPL

          renameVec = RenameVecConst (SC NonConstDescr) (TC NonConstDescr)

      return $ VPropTriple (DBVConst d1 constCols) renameVec renameVec

