{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Optimizer.VL.Properties.Const where

import Data.List
import Text.Printf

import Database.DSH.Impossible

import Database.Algebra.VL.Data
import Database.DSH.Optimizer.VL.Properties.Common
import Database.DSH.Optimizer.VL.Properties.Types

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

fromRenameVec :: ConstVec -> Either String (SourceConstDescr, TargetConstDescr)
fromRenameVec (RenameVecConst s t) = Right (s, t)
fromRenameVec x                    = Left ("Properties.Const fromRenameVec " ++ (show x))

fromPropVec :: ConstVec -> Either String (SourceConstDescr, TargetConstDescr)
fromPropVec (PropVecConst s t)  = Right (s, t)
fromPropVec _                   = Left "Properties.Const fromPropVec"

constExpr1 :: [ConstPayload] -> Expr1 -> Either String ConstPayload
constExpr1 constCols e = 
    case e of
        Constant1 v      -> return $ ConstPL v
        Column1 i        -> if length constCols < i - 1
                            then Left (printf "constExpr1 %s %d" (show constCols) i)
                            else return $ constCols !! (i - 1)
        -- FIXME implement constant folding
        BinApp1 op e1 e2 -> return NonConstPL
        UnApp1 op e1     -> return NonConstPL

inferConstVecNullOp :: NullOp -> Either String (VectorProp ConstVec)
inferConstVecNullOp op =
  case op of
    SingletonDescr                    -> return $ VProp $ DBVConst (ConstDescr $ N 1) []
    -- do not include the first two columns in the payload columns because they represent descr and pos.
    Lit colTypes rows      ->
      if null rows
      then return $ VProp $ DBVConst NonConstDescr $ map (const NonConstPL) colTypes
      else return $ VProp $ DBVConst (ConstDescr $ N 1) constCols
        where constCols       = map toConstPayload $ drop 2 $ transpose rows

              toConstPayload col@(c : _) = if all (c ==) col
                                           then ConstPL c
                                           else NonConstPL
              toConstPayload []          = NonConstPL

    TableRef              _ cols _    -> return $ VProp $ DBVConst (ConstDescr $ N 1) $ map (const NonConstPL) cols

inferConstVecUnOp :: (VectorProp ConstVec) -> UnOp -> Either String (VectorProp ConstVec)
inferConstVecUnOp c op =
  case op of
    UniqueS -> return c

    Aggr _ -> do
      return $ VProp $ DBVConst NonConstDescr [NonConstPL]

    DescToRename -> do
      (d, _) <- unp c >>= fromDBV
      return $ VProp $ RenameVecConst (SC NonConstDescr) (TC d)

    Segment -> do
      (_, constCols) <- unp c >>= fromDBV
      return $ VProp $ DBVConst NonConstDescr constCols

    Unsegment -> do
      (_, constCols) <- unp c >>= fromDBV
      return $ VProp $ DBVConst NonConstDescr constCols

    SelectPos1 _ _ -> do
      (d, cols) <- unp c >>= fromDBV
      return $ VPropPair (DBVConst d cols) (PropVecConst (SC NonConstDescr) (TC NonConstDescr))

    SelectPos1S _ _ -> do
      (d, cols) <- unp c >>= fromDBV
      return $ VPropPair (DBVConst d cols) (PropVecConst (SC NonConstDescr) (TC NonConstDescr))

    Reverse -> do
      (d, cs) <- unp c >>= fromDBV
      return $ VPropPair (DBVConst d cs) (PropVecConst (SC NonConstDescr) (TC NonConstDescr))

    ReverseS -> do
      (d, cs) <- unp c >>= fromDBV
      return $ VPropPair (DBVConst d cs) (PropVecConst (SC NonConstDescr) (TC NonConstDescr))

    FalsePositions -> do
      (d, _) <- unp c >>= fromDBV
      return $ VProp $ DBVConst d [NonConstPL]

    ProjectRename (targetIS, _)  -> do
      -- FIXME this is not precise -- take care of the source space.
      (d, _) <- unp c >>= fromDBV
      let d' = case targetIS of
            STDescrCol -> d
            STPosCol -> NonConstDescr
            STNumber -> NonConstDescr
      return $ VProp $ RenameVecConst (SC NonConstDescr) (TC d')

    Project projExprs   -> do
      (constDescr, constCols) <- unp c >>= fromDBV
      constCols'              <- mapM (constExpr1 constCols) projExprs
      return $ VProp $ DBVConst constDescr constCols'

    Select _       -> do
      (d, cols) <- unp c >>= fromDBV
      return $ VProp $ DBVConst d cols

    Only             -> $unimplemented
    Singleton        -> $unimplemented

    GroupAggr g as -> do
      (d, _) <- unp c >>= fromDBV
      return $ VProp $ DBVConst d (map (const NonConstPL) [ 1 .. (length g) + (length as) ])
      
    Number -> do
      (d, _) <- unp c >>= fromDBV
      return $ VProp $ DBVConst d [NonConstPL]

    NumberS -> do
      (d, _) <- unp c >>= fromDBV
      return $ VProp $ DBVConst d [NonConstPL]

    SortSimple _ -> do
      (d, cs) <- unp c >>= fromDBV
      return $ VPropPair (DBVConst d cs) (PropVecConst (SC NonConstDescr) (TC NonConstDescr))

    GroupSimple es -> do
      (d, cs) <- unp c >>= fromDBV
      return $ VPropTriple (DBVConst d (map (const NonConstPL) es))
                           (DBVConst NonConstDescr (map (const NonConstPL) cs))
                           (PropVecConst (SC NonConstDescr) (TC NonConstDescr))

    Transpose -> do
      (_, cols) <- unp c >>= fromDBV
      return $ VPropPair (DBVConst NonConstDescr []) (DBVConst NonConstDescr cols)
    Reshape _ -> do
      (_, cols) <- unp c >>= fromDBV
      return $ VPropPair (DBVConst NonConstDescr []) (DBVConst NonConstDescr cols)
    ReshapeS _ -> do
      (_, cols) <- unp c >>= fromDBV
      return $ VPropPair (DBVConst NonConstDescr []) (DBVConst NonConstDescr cols)

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
      (dq, cols1) <- unp c1 >>= fromDBV
      (_, cols2) <- unp c2 >>= fromDBV
      return $ VPropTriple (DBVConst dq cols1) 
                           (DBVConst NonConstDescr cols2) 
                           (PropVecConst (SC NonConstDescr) (TC NonConstDescr))

    Sort -> do
      (d, cols) <- unp c2 >>= fromDBV
      return $ VPropPair  (DBVConst d cols) (PropVecConst (SC NonConstDescr) (TC NonConstDescr))

    -- FIXME use cardinality property to infer the length if possible
    -- FIXME handle special cases: empty input, cardinality 1 and const input, ...
    AggrS _ -> do
      return $ VProp $ DBVConst NonConstDescr [NonConstPL]

    DistPrim -> do
      (d, _)    <- unp c2 >>= fromDBV
      (_, cols) <- unp c1 >>= fromDBV
      return $ VPropPair (DBVConst d cols) (PropVecConst (SC NonConstDescr) (TC NonConstDescr))

    DistDesc -> do
      (_, cols) <- unp c1 >>= fromDBV
      return $ VPropPair (DBVConst NonConstDescr cols) (PropVecConst (SC NonConstDescr) (TC NonConstDescr))

    DistSeg -> do
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

    Restrict -> do
      (d, cols) <- unp c1 >>= fromDBV
      return $ VPropPair (DBVConst d cols) (RenameVecConst (SC NonConstDescr) (TC NonConstDescr))

    BinExpr _ -> do
      (d1, _) <- unp c1 >>= fromDBV
      (_, _) <- unp c2 >>= fromDBV

      return $ VProp $ DBVConst d1 [NonConstPL]

    SelectPos _ -> do
      (d1, cols1) <- unp c1 >>= fromDBV

      return $ VPropPair (DBVConst d1 cols1) (RenameVecConst (SC NonConstDescr) (TC NonConstDescr))

    SelectPosS _ -> do
      (d1, cols1) <- unp c1 >>= fromDBV

      return $ VPropPair (DBVConst d1 cols1) (RenameVecConst (SC NonConstDescr) (TC NonConstDescr))

    Zip -> do
      (d1, cols1) <- unp c1 >>= fromDBV
      (_, cols2)  <- unp c2 >>= fromDBV

      let cols = cols1 ++ cols2

      return $ VProp $ DBVConst d1 cols

    ZipS -> do
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

    CartProductS -> do
      (_, cols1) <- unp c1 >>= fromDBV
      (_, cols2) <- unp c2 >>= fromDBV

      let constCols = cols1 ++ cols2

      -- FIXME check propVec components for correctness/preciseness
      let propVec = PropVecConst (SC NonConstDescr) (TC NonConstDescr)

      -- FIXME descr = 1 is almost certainly not correct
      return $ VPropTriple (DBVConst (ConstDescr $ N 1) constCols) propVec propVec

    NestProductS -> do
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

    EquiJoinS _ _ -> do
      (_, cols1) <- unp c1 >>= fromDBV
      (_, cols2) <- unp c2 >>= fromDBV

      let constCols = cols1 ++ cols2

      -- FIXME check propVec components for correctness/preciseness
      let propVec = PropVecConst (SC NonConstDescr) (TC NonConstDescr)

      -- FIXME descr = 1 is almost certainly not correct
      return $ VPropTriple (DBVConst (ConstDescr $ N 1) constCols) propVec propVec

    NestJoinS _ _ -> do
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

    SemiJoinS _ _ -> do
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

    AntiJoinS _ _ -> do
      (_, cols1) <- unp c1 >>= fromDBV
      
      -- FIXME This is propably too pessimistic for the source descriptor
      let renameVec = RenameVecConst (SC NonConstDescr) (TC NonConstDescr)
  
      -- FIXME This is propably too pessimistic for the descr 
      return $ VPropPair (DBVConst NonConstDescr cols1) renameVec

    TransposeS -> do
      (_, cols2) <- unp c2 >>= fromDBV
      return $ VPropPair (DBVConst NonConstDescr []) (DBVConst NonConstDescr cols2)

inferConstVecTerOp :: (VectorProp ConstVec) -> (VectorProp ConstVec) -> (VectorProp ConstVec) -> TerOp -> Either String (VectorProp ConstVec)
inferConstVecTerOp c1 c2 c3 op =
  case op of
    Combine -> do
      (d1, _) <- unp c1 >>= fromDBV
      (_, cols2)  <- unp c2 >>= fromDBV
      (_, cols3)  <- unp c3 >>= fromDBV

      let constCols = map sameConst $ zip cols2 cols3

          sameConst ((ConstPL v1), (ConstPL v2)) | v1 == v2 = ConstPL v1
          sameConst (_, _)                                  = NonConstPL

          renameVec = RenameVecConst (SC NonConstDescr) (TC NonConstDescr)

      return $ VPropTriple (DBVConst d1 constCols) renameVec renameVec

