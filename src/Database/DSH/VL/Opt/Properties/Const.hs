{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.VL.Opt.Properties.Const
    ( inferConstVecNullOp
    , inferConstVecUnOp
    , inferConstVecBinOp
    , inferConstVecTerOp
    ) where

import           Control.Monad
import           Data.List
import qualified Data.List.NonEmpty                          as N
import           Data.Maybe

import Database.DSH.Common.Impossible
import           Database.DSH.VL.Opt.Properties.Common
import           Database.DSH.VL.Opt.Properties.Types
import           Database.DSH.VL.Lang
import           Database.DSH.Common.Lang

unp :: Show a => VectorProp a -> Either String a
unp = unpack "Properties.Const"

fromDBV :: ConstVec -> Either String [ConstPayload]
fromDBV (ConstVec pl) = Right pl
fromDBV CNA           = Left $ "Properties.Const.fromDBV"

--------------------------------------------------------------------------------
-- Evaluation of constant expressions

-- FIXME finish remaining cases, only integer numeric operations so
-- far.

mkEnv :: [ConstPayload] -> [(DBCol, ScalarVal)]
mkEnv constCols = mapMaybe envEntry $ zip [1..] constCols
  where
    envEntry :: (DBCol, ConstPayload) -> Maybe (DBCol, ScalarVal)
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

evalBinOp :: ScalarBinOp -> ScalarVal -> ScalarVal -> Maybe ScalarVal
evalBinOp (SBNumOp nop)  (IntV i1)    (IntV i2)    = return $ IntV $ evalNumOp nop i1 i2
evalBinOp (SBNumOp _)    (DoubleV _)  (DoubleV _)  = mzero
evalBinOp (SBNumOp _)    (DecimalV _) (DecimalV _) = mzero

evalBinOp (SBRelOp _)    (IntV _)     (IntV _)     = mzero
evalBinOp (SBRelOp _)    (DoubleV _)  (DoubleV _)  = mzero
evalBinOp (SBRelOp _)    (DecimalV _) (DecimalV _) = mzero
evalBinOp (SBRelOp _)    (StringV _)  (StringV _)  = mzero
evalBinOp (SBRelOp _)    (DateV _)    (DateV _)    = mzero

evalBinOp (SBBoolOp _)   (BoolV _)    (BoolV _)    = mzero
evalBinOp (SBStringOp _) (StringV _)  (StringV _)  = mzero
evalBinOp (SBDateOp _)   (IntV _)     (DateV _)    = mzero
evalBinOp (SBDateOp _)   (DateV _)    (DateV _)    = mzero
evalBinOp _              _            _            = $impossible

evalUnOp :: ScalarUnOp -> ScalarVal -> Maybe ScalarVal
evalUnOp _ _ = mzero

constExpr :: [ConstPayload] -> Expr -> Either String ConstPayload
constExpr constCols expr =
    case eval expr of
        Just v  -> return $ ConstPL v
        Nothing -> return NonConstPL

  where
    env :: [(DBCol, ScalarVal)]
    env = mkEnv constCols

    eval :: Expr -> Maybe ScalarVal
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
            BoolV True  -> eval t
            BoolV False -> eval e
            _           -> mzero

--------------------------------------------------------------------------------
-- Stuff

inferConstVecNullOp :: NullOp -> Either String (VectorProp ConstVec)
inferConstVecNullOp op =
  case op of
    SingletonDescr                    -> return $ VProp $ ConstVec []
    -- do not include the first two columns in the payload columns because they represent descr and pos.
    Lit (_, colTypes, rows)      ->
      if null rows
      then return $ VProp $ ConstVec $ map (const NonConstPL) colTypes
      else return $ VProp $ ConstVec constCols
        where constCols       = map toConstPayload $ drop 2 $ transpose rows

              toConstPayload col@(c : _) = if all (c ==) col
                                           then ConstPL c
                                           else NonConstPL
              toConstPayload []          = NonConstPL

    TableRef (_, schema)    -> return $ VProp
                                      $ ConstVec
                                      $ map (const NonConstPL)
                                      $ N.toList
                                      $ tableCols schema

inferConstVecUnOp :: (VectorProp ConstVec) -> UnOp -> Either String (VectorProp ConstVec)
inferConstVecUnOp c op =
  case op of
    WinFun _ -> do
      cols <- unp c >>= fromDBV
      return $ VProp $ ConstVec (cols ++ [NonConstPL])

    UniqueS -> return c
    Unique -> return c

    Aggr _ -> do
      return $ VProp $ ConstVec [NonConstPL]

    AggrNonEmpty _ -> do
      return $ VProp $ ConstVec [NonConstPL]

    UnboxKey -> return $ VProp CNA

    Segment -> do
      constCols <- unp c >>= fromDBV
      return $ VProp $ ConstVec constCols

    Unsegment -> do
      constCols <- unp c >>= fromDBV
      return $ VProp $ ConstVec constCols

    Reverse -> do
      cs <- unp c >>= fromDBV
      return $ VPropPair (ConstVec cs) CNA

    ReverseS -> do
      cs <- unp c >>= fromDBV
      return $ VPropPair (ConstVec cs) CNA

    Project projExprs   -> do
      constCols  <- unp c >>= fromDBV
      constCols' <- mapM (constExpr constCols) projExprs
      return $ VProp $ ConstVec constCols'

    Select _       -> do
      cols <- unp c >>= fromDBV
      return $ VPropPair (ConstVec cols) CNA

    GroupAggr (g, as) -> do
      let pl = [ NonConstPL | _ <- [1 .. (length g) + (N.length as)] ]
      return $ VProp $ ConstVec pl

    Number -> do
      cols <- unp c >>= fromDBV
      return $ VProp $ ConstVec (cols ++ [NonConstPL])

    NumberS -> do
      cols <- unp c >>= fromDBV
      return $ VProp $ ConstVec (cols ++ [NonConstPL])

    Sort _ -> do
      cs <- unp c >>= fromDBV
      return $ VPropPair (ConstVec cs) CNA

    SortS _ -> do
      cs <- unp c >>= fromDBV
      return $ VPropPair (ConstVec cs) CNA

    Group es -> do
      cs <- unp c >>= fromDBV
      return $ VPropTriple (ConstVec (map (const NonConstPL) es))
                           (ConstVec (map (const NonConstPL) cs))
                           CNA

    GroupS es -> do
      cs <- unp c >>= fromDBV
      return $ VPropTriple (ConstVec (map (const NonConstPL) es))
                           (ConstVec (map (const NonConstPL) cs))
                           CNA

    Transpose -> do
      cols <- unp c >>= fromDBV
      return $ VPropPair (ConstVec []) (ConstVec cols)
    Reshape _ -> do
      cols <- unp c >>= fromDBV
      return $ VPropPair (ConstVec []) (ConstVec cols)
    ReshapeS _ -> do
      cols <- unp c >>= fromDBV
      return $ VPropPair (ConstVec []) (ConstVec cols)

    AggrNonEmptyS _ -> do
      return $ VProp $ ConstVec [NonConstPL]

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
    -- FIXME use cardinality property to infer the length if possible
    -- FIXME handle special cases: empty input, cardinality 1 and const input, ...
    AggrS _ -> do
      return $ VProp $ ConstVec [NonConstPL]

    DistLift -> do
      cols1 <- unp c1 >>= fromDBV
      cols2 <- unp c2 >>= fromDBV
      return $ VPropPair (ConstVec (cols1 ++ cols2)) CNA

    AppKey -> do
      cols <- unp c2 >>= fromDBV
      return $ VPropPair (ConstVec cols) CNA

    AppSort -> do
      cols <- unp c2 >>= fromDBV
      return $ VPropPair (ConstVec cols) CNA

    AppFilter -> do
      cols <- unp c2 >>= fromDBV
      return $ VPropPair (ConstVec cols) CNA

    AppRep -> do
      cols <- unp c2 >>= fromDBV
      return $ VPropPair (ConstVec cols) CNA

    UnboxScalar -> do
      cols1 <- unp c1 >>= fromDBV
      cols2 <- unp c2 >>= fromDBV
      return $ VProp $ ConstVec (cols1 ++ cols2)

    Append -> do
      cols1 <- unp c1 >>= fromDBV
      cols2 <- unp c2 >>= fromDBV

      let constCols = map sameConst $ zip cols1 cols2

          sameConst ((ConstPL v1), (ConstPL v2)) | v1 == v2 = ConstPL v1
          sameConst (_, _)                                  = NonConstPL

      return $ VPropTriple (ConstVec constCols) CNA CNA

    AppendS -> do
      cols1 <- unp c1 >>= fromDBV
      cols2 <- unp c2 >>= fromDBV

      let constCols = map sameConst $ zip cols1 cols2

          sameConst ((ConstPL v1), (ConstPL v2)) | v1 == v2 = ConstPL v1
          sameConst (_, _)                                  = NonConstPL

      return $ VPropTriple (ConstVec constCols) CNA CNA

    Align -> do
      cols1 <- unp c1 >>= fromDBV
      cols2  <- unp c2 >>= fromDBV
      let cols = cols1 ++ cols2
      return $ VProp $ ConstVec cols

    Zip -> do
      cols1 <- unp c1 >>= fromDBV
      cols2  <- unp c2 >>= fromDBV
      let cols = cols1 ++ cols2
      return $ VPropTriple (ConstVec cols) CNA CNA

    ZipS -> do
      cols1 <- unp c1 >>= fromDBV
      cols2  <- unp c2 >>= fromDBV
      let cols = cols1 ++ cols2
      return $ VPropTriple (ConstVec cols) CNA CNA

    CartProduct -> do
      cols1 <- unp c1 >>= fromDBV
      cols2 <- unp c2 >>= fromDBV
      let constCols = cols1 ++ cols2
      return $ VPropTriple (ConstVec constCols) CNA CNA

    CartProductS -> do
      cols1 <- unp c1 >>= fromDBV
      cols2 <- unp c2 >>= fromDBV
      let constCols = cols1 ++ cols2
      return $ VPropTriple (ConstVec constCols) CNA CNA

    NestProductS -> do
      cols1 <- unp c1 >>= fromDBV
      cols2 <- unp c2 >>= fromDBV
      let constCols = cols1 ++ cols2
      return $ VPropTriple (ConstVec constCols) CNA CNA

    NestJoin _ -> do
      cols1 <- unp c1 >>= fromDBV
      cols2 <- unp c2 >>= fromDBV
      let constCols = cols1 ++ cols2
      return $ VPropTriple (ConstVec constCols) CNA CNA

    GroupJoin _ -> do
      cols1 <- unp c1 >>= fromDBV
      let constCols = cols1 ++ [NonConstPL]
      return $ VProp (ConstVec constCols)

    NestProduct -> do
      cols1 <- unp c1 >>= fromDBV
      cols2 <- unp c2 >>= fromDBV
      let constCols = cols1 ++ cols2
      return $ VPropTriple (ConstVec constCols) CNA CNA

    ThetaJoin _ -> do
      cols1 <- unp c1 >>= fromDBV
      cols2 <- unp c2 >>= fromDBV

      let constCols = cols1 ++ cols2

      return $ VPropTriple (ConstVec constCols) CNA CNA

    ThetaJoinS _ -> do
      cols1 <- unp c1 >>= fromDBV
      cols2 <- unp c2 >>= fromDBV
      let constCols = cols1 ++ cols2
      return $ VPropTriple (ConstVec constCols) CNA CNA

    NestJoinS _ -> do
      cols1 <- unp c1 >>= fromDBV
      cols2 <- unp c2 >>= fromDBV
      let constCols = cols1 ++ cols2
      return $ VPropTriple (ConstVec constCols) CNA CNA

    SemiJoin _ -> do
      cols1 <- unp c1 >>= fromDBV
      return $ VPropPair (ConstVec cols1) CNA

    SemiJoinS _ -> do
      cols1 <- unp c1 >>= fromDBV
      return $ VPropPair (ConstVec cols1) CNA

    AntiJoin _ -> do
      cols1 <- unp c1 >>= fromDBV
      return $ VPropPair (ConstVec cols1) CNA

    AntiJoinS _ -> do
      cols1 <- unp c1 >>= fromDBV
      return $ VPropPair (ConstVec cols1) CNA

    TransposeS -> do
      cols2 <- unp c2 >>= fromDBV
      return $ VPropPair (ConstVec []) (ConstVec cols2)

inferConstVecTerOp :: VectorProp ConstVec
                   -> VectorProp ConstVec
                   -> VectorProp ConstVec
                   -> TerOp
                   -> Either String (VectorProp ConstVec)
inferConstVecTerOp _c1 c2 c3 op =
  case op of
    Combine -> do
      cols2  <- unp c2 >>= fromDBV
      cols3  <- unp c3 >>= fromDBV

      let constCols = map sameConst $ zip cols2 cols3

          sameConst ((ConstPL v1), (ConstPL v2)) | v1 == v2 = ConstPL v1
          sameConst (_, _)                                  = NonConstPL

      return $ VPropTriple (ConstVec constCols) CNA CNA

