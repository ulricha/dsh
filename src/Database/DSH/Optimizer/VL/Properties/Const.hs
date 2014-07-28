{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Optimizer.VL.Properties.Const where

import           Control.Monad
import           Data.List
import qualified Data.List.NonEmpty                          as N
import           Data.Maybe

import Database.DSH.Impossible
import           Database.DSH.Optimizer.VL.Properties.Common
import           Database.DSH.Optimizer.VL.Properties.Types
import           Database.DSH.VL.Lang
import           Database.DSH.Common.Lang

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

fromRVec :: ConstVec -> Either String (SourceConstDescr, TargetConstDescr)
fromRVec (RenameVecConst s t) = Right (s, t)
fromRVec x                    = Left ("Properties.Const fromRVec " ++ (show x))

fromPVec :: ConstVec -> Either String (SourceConstDescr, TargetConstDescr)
fromPVec (PropVecConst s t)  = Right (s, t)
fromPVec _                   = Left "Properties.Const fromPVec"

--------------------------------------------------------------------------------
-- Evaluation of constant expressions

-- FIXME finish remaining cases, only integer numeric operations so
-- far.

mkEnv :: [ConstPayload] -> [(DBCol, VLVal)]
mkEnv constCols = mapMaybe envEntry $ zip [1..] constCols
  where
    envEntry :: (DBCol, ConstPayload) -> Maybe (DBCol, VLVal)
    envEntry (_, NonConstPL) = mzero
    envEntry (c, ConstPL v)  = return (c, v)

evalNumOp :: BinNumOp -> Int -> Int -> Int
evalNumOp op v1 v2 =
    case op of
        Add -> v1 + v2
        Sub -> v1 - v2
        Div -> v1 `div` v2
        Mul -> v1 * v2
        Mod -> v1 `mod` v2

evalBinOp :: ScalarBinOp -> VLVal -> VLVal -> Maybe VLVal
evalBinOp op v1 v2 =
    case (v1, v2) of
        (VLInt i1, VLInt i2)       ->
            case op of
                SBNumOp nop  -> return $ VLInt $ evalNumOp nop i1 i2
                SBRelOp _    -> mzero
                SBBoolOp _   -> $impossible
                SBStringOp _ -> $impossible
                
        (VLBool _, VLBool _)     ->
            case op of
                SBBoolOp _   -> mzero
                SBRelOp _    -> mzero
                SBNumOp _    -> $impossible
                SBStringOp _ -> $impossible
        (VLString _, VLString _) ->
            case op of
                SBRelOp _    -> mzero
                SBStringOp _ -> mzero
                SBBoolOp _   -> $impossible
                SBNumOp _    -> $impossible
        (VLDouble _, VLDouble _) ->
            case op of
                SBRelOp _    -> mzero
                SBNumOp _    -> mzero
                SBBoolOp _   -> $impossible
                SBStringOp _ -> $impossible
        (VLUnit, VLUnit)           -> mzero
        _                          -> $impossible

evalUnOp :: ScalarUnOp -> VLVal -> Maybe VLVal
evalUnOp _ _ = mzero

constExpr :: [ConstPayload] -> Expr -> Either String ConstPayload
constExpr constCols expr =
    case eval expr of
        Just v  -> return $ ConstPL v
        Nothing -> return NonConstPL

  where
    env :: [(DBCol, VLVal)]
    env = mkEnv constCols

    eval :: Expr -> Maybe VLVal
    eval (Constant v)      = return v
    eval (Column i)        = lookup i env
    eval (BinApp op e1 e2) = do
        v1 <- eval e1
        v2 <- eval e2
        evalBinOp op v1 v2
    eval (UnApp op e1)     = do
        v <- eval e1
        evalUnOp op v
    eval (If c t e)        = do
        cv <- eval c
        case cv of
            VLBool True  -> eval t
            VLBool False -> eval e
            _            -> mzero

--------------------------------------------------------------------------------
-- Stuff

nonConstPVec :: ConstVec
nonConstPVec = PropVecConst (SC NonConstDescr) (TC NonConstDescr)

nonConstRVec :: ConstVec
nonConstRVec = RenameVecConst (SC NonConstDescr) (TC NonConstDescr)

inferConstVecNullOp :: NullOp -> Either String (VectorProp ConstVec)
inferConstVecNullOp op =
  case op of
    SingletonDescr                    -> return $ VProp $ DBVConst (ConstDescr $ N 1) []
    -- do not include the first two columns in the payload columns because they represent descr and pos.
    Lit _ colTypes rows      ->
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

    AggrNonEmpty _ -> do
      return $ VProp $ DBVConst (ConstDescr (N 1)) [NonConstPL]

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
      return $ VPropTriple (DBVConst d cols) 
                           (RenameVecConst (SC NonConstDescr) (TC NonConstDescr))
                           (RenameVecConst (SC NonConstDescr) (TC NonConstDescr))

    SelectPos1S _ _ -> do
      (d, cols) <- unp c >>= fromDBV
      return $ VPropTriple (DBVConst d cols) 
                           (RenameVecConst (SC NonConstDescr) (TC NonConstDescr))
                           (RenameVecConst (SC NonConstDescr) (TC NonConstDescr))

    Reverse -> do
      (d, cs) <- unp c >>= fromDBV
      return $ VPropPair (DBVConst d cs) (PropVecConst (SC NonConstDescr) (TC NonConstDescr))

    ReverseS -> do
      (d, cs) <- unp c >>= fromDBV
      return $ VPropPair (DBVConst d cs) (PropVecConst (SC NonConstDescr) (TC NonConstDescr))

    Project projExprs   -> do
      (constDescr, constCols) <- unp c >>= fromDBV
      constCols'              <- mapM (constExpr constCols) projExprs
      return $ VProp $ DBVConst constDescr constCols'

    Select _       -> do
      (d, cols) <- unp c >>= fromDBV
      return $ VPropPair (DBVConst d cols) (RenameVecConst (SC NonConstDescr) (TC NonConstDescr))

    GroupAggr (g, as) -> do
      (d, _) <- unp c >>= fromDBV
      return $ VProp $ DBVConst d (map (const NonConstPL) [ 1 .. (length g) + (N.length as) ])

    Number -> do
      (d, cols) <- unp c >>= fromDBV
      return $ VProp $ DBVConst d (cols ++ [NonConstPL])

    NumberS -> do
      (d, cols) <- unp c >>= fromDBV
      return $ VProp $ DBVConst d (cols ++ [NonConstPL])

    SortScalarS _ -> do
      (d, cs) <- unp c >>= fromDBV
      return $ VPropPair (DBVConst d cs) (PropVecConst (SC NonConstDescr) (TC NonConstDescr))

    GroupScalarS es -> do
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

    SortS -> do
      (d, cols) <- unp c2 >>= fromDBV
      return $ VPropPair  (DBVConst d cols) (PropVecConst (SC NonConstDescr) (TC NonConstDescr))

    -- FIXME use cardinality property to infer the length if possible
    -- FIXME handle special cases: empty input, cardinality 1 and const input, ...
    AggrS _ -> do
      return $ VProp $ DBVConst NonConstDescr [NonConstPL]

    AggrNonEmptyS _ -> do
      return $ VProp $ DBVConst NonConstDescr [NonConstPL]

    DistPrim -> do
      (d, _)    <- unp c2 >>= fromDBV
      (_, cols) <- unp c1 >>= fromDBV
      return $ VPropPair (DBVConst d cols) (PropVecConst (SC NonConstDescr) (TC NonConstDescr))

    DistDesc -> do
      (_, cols) <- unp c1 >>= fromDBV
      return $ VPropPair (DBVConst NonConstDescr cols) (PropVecConst (SC NonConstDescr) (TC NonConstDescr))

    Align -> do
      (_, cols1) <- unp c1 >>= fromDBV
      (d, cols2) <- unp c2 >>= fromDBV
      return $ VPropPair (DBVConst d (cols1 ++ cols2)) (PropVecConst (SC NonConstDescr) (TC NonConstDescr))

    PropRename -> do
      (_, cols) <- unp c2 >>= fromDBV
      (SC _, TC target) <- unp c1 >>= fromRVec

      return $ VProp $ DBVConst target cols

    PropFilter -> do
      (_, cols) <- unp c2 >>= fromDBV
      (SC _, TC target) <- unp c1 >>= fromRVec

      return $ VPropPair (DBVConst target cols) (RenameVecConst (SC NonConstDescr) (TC NonConstDescr))

    PropReorder -> do
      (_, cols) <- unp c2 >>= fromDBV
      (SC _, TC target) <- unp c1 >>= fromPVec

      return $ VPropPair (DBVConst target cols) (PropVecConst (SC NonConstDescr) (TC NonConstDescr))

    Unbox -> do
      (_, TC descr) <- unp c1 >>= fromRVec
      (_, cols)     <- unp c2 >>= fromDBV

      return $ VPropPair (DBVConst descr cols) (RenameVecConst (SC NonConstDescr) (TC NonConstDescr))

    Append -> do
      (d1, cols1) <- unp c1 >>= fromDBV
      (d2, cols2) <- unp c2 >>= fromDBV

      let constCols = map sameConst $ zip cols1 cols2

          sameConst ((ConstPL v1), (ConstPL v2)) | v1 == v2 = ConstPL v1
          sameConst (_, _)                                  = NonConstPL

          d = case (d1, d2) of
            (ConstDescr n1, ConstDescr n2) | n1 == n2 -> ConstDescr n1
            _                                         -> NonConstDescr

      return $ VPropTriple (DBVConst d constCols) nonConstRVec nonConstRVec

    AppendS -> do
      (d1, cols1) <- unp c1 >>= fromDBV
      (d2, cols2) <- unp c2 >>= fromDBV

      let constCols = map sameConst $ zip cols1 cols2

          sameConst ((ConstPL v1), (ConstPL v2)) | v1 == v2 = ConstPL v1
          sameConst (_, _)                                  = NonConstPL

          d = case (d1, d2) of
            (ConstDescr n1, ConstDescr n2) | n1 == n2 -> ConstDescr n1
            _                                         -> NonConstDescr

      return $ VPropTriple (DBVConst d constCols) nonConstRVec nonConstRVec

    Restrict -> do
      (d, cols) <- unp c1 >>= fromDBV
      return $ VPropPair (DBVConst d cols) (RenameVecConst (SC NonConstDescr) (TC NonConstDescr))

    SelectPos _ -> do
      (d1, cols1) <- unp c1 >>= fromDBV

      return $ VPropTriple (DBVConst d1 cols1) 
                           (RenameVecConst (SC NonConstDescr) (TC NonConstDescr))
                           (RenameVecConst (SC NonConstDescr) (TC NonConstDescr))

    SelectPosS _ -> do
      (d1, cols1) <- unp c1 >>= fromDBV

      return $ VPropTriple (DBVConst d1 cols1) 
                           (RenameVecConst (SC NonConstDescr) (TC NonConstDescr))
                           (RenameVecConst (SC NonConstDescr) (TC NonConstDescr))

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
      -- FIXME descr = 1 is almost certainly not correct
      return $ VPropTriple (DBVConst (ConstDescr $ N 1) constCols) nonConstPVec nonConstPVec

    CartProductS -> do
      (_, cols1) <- unp c1 >>= fromDBV
      (_, cols2) <- unp c2 >>= fromDBV

      let constCols = cols1 ++ cols2

      -- FIXME check propVec components for correctness/preciseness
      -- FIXME descr = 1 is almost certainly not correct
      return $ VPropTriple (DBVConst (ConstDescr $ N 1) constCols) nonConstPVec nonConstPVec

    NestProductS -> do
      (_, cols1) <- unp c1 >>= fromDBV
      (_, cols2) <- unp c2 >>= fromDBV

      let constCols = cols1 ++ cols2

      -- FIXME check propVec components for correctness/preciseness
      -- FIXME descr = 1 is almost certainly not correct
      return $ VPropTriple (DBVConst (ConstDescr $ N 1) constCols) nonConstPVec nonConstPVec

    ThetaJoin _ -> do
      (_, cols1) <- unp c1 >>= fromDBV
      (_, cols2) <- unp c2 >>= fromDBV

      let constCols = cols1 ++ cols2

      -- FIXME check propVec components for correctness/preciseness
      -- FIXME descr = 1 is almost certainly not correct
      return $ VPropTriple (DBVConst (ConstDescr $ N 1) constCols) nonConstPVec nonConstPVec

    ThetaJoinS _ -> do
      (_, cols1) <- unp c1 >>= fromDBV
      (_, cols2) <- unp c2 >>= fromDBV

      let constCols = cols1 ++ cols2

      -- FIXME check propVec components for correctness/preciseness
      -- FIXME descr = 1 is almost certainly not correct
      return $ VPropTriple (DBVConst (ConstDescr $ N 1) constCols) nonConstPVec nonConstPVec

    NestJoinS _ -> do
      (_, cols1) <- unp c1 >>= fromDBV
      (_, cols2) <- unp c2 >>= fromDBV

      let constCols = cols1 ++ cols2

      -- FIXME check propVec components for correctness/preciseness
      -- FIXME descr = 1 is almost certainly not correct
      return $ VPropTriple (DBVConst (ConstDescr $ N 1) constCols) nonConstPVec nonConstPVec

    SemiJoin _ -> do
      (_, cols1) <- unp c1 >>= fromDBV

      -- FIXME This is propably too pessimistic for the source descriptor
      let renameVec = RenameVecConst (SC NonConstDescr) (TC NonConstDescr)

      -- FIXME This is propably too pessimistic for the descr
      return $ VPropPair (DBVConst NonConstDescr cols1) renameVec

    SemiJoinS _ -> do
      (_, cols1) <- unp c1 >>= fromDBV

      -- FIXME This is propably too pessimistic for the source descriptor
      let renameVec = RenameVecConst (SC NonConstDescr) (TC NonConstDescr)

      -- FIXME This is propably too pessimistic for the descr
      return $ VPropPair (DBVConst NonConstDescr cols1) renameVec

    AntiJoin _ -> do
      (_, cols1) <- unp c1 >>= fromDBV

      -- FIXME This is propably too pessimistic for the source descriptor
      let renameVec = RenameVecConst (SC NonConstDescr) (TC NonConstDescr)

      -- FIXME This is propably too pessimistic for the descr
      return $ VPropPair (DBVConst NonConstDescr cols1) renameVec

    AntiJoinS _ -> do
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

