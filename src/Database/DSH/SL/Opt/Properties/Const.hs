{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.SL.Opt.Properties.Const
    ( inferConstVecNullOp
    , inferConstVecUnOp
    , inferConstVecBinOp
    , inferConstVecTerOp
    ) where

import           Control.Monad
import qualified Data.Foldable                         as F
import qualified Data.List.NonEmpty                    as N
import           Data.Maybe
import qualified Data.Sequence                         as S

import           Database.DSH.Common.Impossible
import           Database.DSH.Common.Lang
import           Database.DSH.Common.VectorLang
import           Database.DSH.SL.Lang
import           Database.DSH.SL.Opt.Properties.Common
import           Database.DSH.SL.Opt.Properties.Types

unp :: Show a => VectorProp a -> Either String a
unp = unpack "Properties.Const"

fromDBV :: ConstVec -> Either String ConstPayload
fromDBV (ConstVec pl) = Right pl
fromDBV CNA           = Left "Properties.Const.fromDBV"

--------------------------------------------------------------------------------
-- Evaluation of constant expressions

-- FIXME finish remaining cases, only integer numeric operations so
-- far.

evalNumOp :: BinNumOp -> Int -> Int -> Int
evalNumOp op v1 v2 =
    case op of
        Add -> v1 + v2
        Sub -> v1 - v2
        Div -> v1 `div` v2
        Mul -> v1 * v2
        Mod -> v1 `mod` v2

evalBinOp :: ScalarBinOp -> ScalarVal -> ScalarVal -> ConstPayload
evalBinOp (SBNumOp nop)  (IntV i1)    (IntV i2)    = CPVal $ IntV $ evalNumOp nop i1 i2
evalBinOp (SBNumOp _)    (DoubleV _)  (DoubleV _)  = CPNoVal
evalBinOp (SBNumOp _)    (DecimalV _) (DecimalV _) = CPNoVal

evalBinOp (SBRelOp _)    (IntV _)     (IntV _)     = CPNoVal
evalBinOp (SBRelOp _)    (DoubleV _)  (DoubleV _)  = CPNoVal
evalBinOp (SBRelOp _)    (DecimalV _) (DecimalV _) = CPNoVal
evalBinOp (SBRelOp _)    (StringV _)  (StringV _)  = CPNoVal
evalBinOp (SBRelOp _)    (DateV _)    (DateV _)    = CPNoVal

evalBinOp (SBBoolOp _)   (BoolV _)    (BoolV _)    = CPNoVal
evalBinOp (SBStringOp _) (StringV _)  (StringV _)  = CPNoVal
evalBinOp (SBDateOp _)   (IntV _)     (DateV _)    = CPNoVal
evalBinOp (SBDateOp _)   (DateV _)    (DateV _)    = CPNoVal
evalBinOp _              _            _            = $impossible

evalUnOp :: ScalarUnOp -> ScalarVal -> ConstPayload
evalUnOp _ _ = CPNoVal

constExpr :: ConstPayload -> TExpr -> ConstPayload
constExpr constInput expr = eval constInput expr

eval :: ConstPayload -> TExpr -> ConstPayload
eval v (VConstant c)       = CPVal c
eval v VInput              = v
eval v (VBinApp op e1 e2)  =
    case (eval v e1, eval v e2) of
        (CPVal v1, CPVal v2) -> evalBinOp op v1 v2
        _                          -> CPNoVal
eval v (VUnApp op e1)      =
    case eval v e1 of
        CPVal v1 -> evalUnOp op v1
        _           -> CPNoVal
eval v (VIf c t e)         =
    case eval v c of
        CPVal (BoolV True)  -> eval v t
        CPVal (BoolV False) -> eval v e
        _                      -> CPNoVal

--------------------------------------------------------------------------------

updateConst :: ConstPayload -> VecVal -> ConstPayload
updateConst (CPTuple cs) (VVTuple vs) = CPTuple $ zipWith updateConst cs vs
updateConst CPNoVal      (VVScalar s) = CPNoVal
updateConst (CPVal s')   (VVScalar s)
    | s == s'                         = CPVal s
    | otherwise                       = CPNoVal
updateConst _            VVIndex      = CPNoVal
updateConst _            _            = $impossible

initConst :: VecVal -> ConstPayload
initConst (VVTuple vs) = CPTuple $ map initConst vs
initConst (VVScalar s) = CPVal s
initConst VVIndex      = CPNoVal

noConst :: PType -> ConstPayload
noConst (PTupleT ts) = CPTuple $ map noConst ts
noConst (PScalarT t) = CPNoVal
noConst PIndexT      = CPNoVal

inferConstVecNullOp :: NullOp -> Either String (VectorProp ConstVec)
inferConstVecNullOp op =
  case op of
    Lit (ty, segs)       ->
        case S.viewl $ segmentData segs of
            v S.:< vs -> return $ VProp $ ConstVec $ F.foldl' updateConst (initConst v) vs
            _         -> return $ VProp $ ConstVec $ noConst ty

    TableRef (_, schema) -> return $ VProp
                                   $ ConstVec
                                   $ CPTuple
                                   $ map (const CPNoVal)
                                   $ N.toList
                                   $ tableCols schema

inferConstVecUnOp :: VectorProp ConstVec -> UnOp -> Either String (VectorProp ConstVec)
inferConstVecUnOp c op =
  case op of
    WinFun _ -> do
      cv <- unp c >>= fromDBV
      return $ VProp $ ConstVec $ CPTuple [cv, CPNoVal]

    Unique -> return c

    UnboxKey -> return $ VProp CNA

    Segment -> do
      constCols <- unp c >>= fromDBV
      return $ VProp $ ConstVec constCols

    Unsegment -> do
      constCols <- unp c >>= fromDBV
      return $ VProp $ ConstVec constCols

    Reverse -> do
      cv <- unp c >>= fromDBV
      return $ VPropPair (ConstVec cv) CNA

    Project projExpr   -> do
      cv <- unp c >>= fromDBV
      let cv' = constExpr cv projExpr
      return $ VProp $ ConstVec cv'

    Select _       -> do
      cols <- unp c >>= fromDBV
      return $ VPropPair (ConstVec cols) CNA

    GroupAggr (groupExpr, aggrFun) -> do
      return $ VProp $ ConstVec $ CPTuple [CPNoVal, CPNoVal]

    Number -> do
      cp <- unp c >>= fromDBV
      return $ VProp $ ConstVec $ CPTuple [cp, CPNoVal]

    Sort _ -> do
      cs <- unp c >>= fromDBV
      return $ VPropPair (ConstVec cs) CNA

    Group es -> do
      cs <- unp c >>= fromDBV
      return $ VPropTriple (ConstVec (map (const NonConstPL) es))
                           (ConstVec (map (const NonConstPL) cs))
                           CNA

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

inferConstVecBinOp :: VectorProp ConstVec -> VectorProp ConstVec -> BinOp -> Either String (VectorProp ConstVec)
inferConstVecBinOp c1 c2 op =
  case op of
    -- FIXME use cardinality property to infer the length if possible
    -- FIXME handle special cases: empty input, cardinality 1 and const input, ...
    Fold _ -> return $ VProp $ ConstVec [NonConstPL]

    ReplicateNest -> do
      cols1 <- unp c1 >>= fromDBV
      cols2 <- unp c2 >>= fromDBV
      return $ VPropPair (ConstVec (cols1 ++ cols2)) CNA

    ReplicateScalar -> do
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

    UnboxSng -> do
      cols1 <- unp c1 >>= fromDBV
      cols2 <- unp c2 >>= fromDBV
      return $ VPropPair (ConstVec (cols1 ++ cols2)) CNA

    Append -> do
      cols1 <- unp c1 >>= fromDBV
      cols2 <- unp c2 >>= fromDBV

      let constCols = zipWith sameConst cols1 cols2

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

    CartProduct -> do
      cols1 <- unp c1 >>= fromDBV
      cols2 <- unp c2 >>= fromDBV
      let constCols = cols1 ++ cols2
      return $ VPropTriple (ConstVec constCols) CNA CNA

    ReplicateVector -> do
      cols1 <- unp c1 >>= fromDBV
      return $ VPropPair (ConstVec cols1) CNA

    GroupJoin _ -> do
      cols1 <- unp c1 >>= fromDBV
      let constCols = cols1 ++ [NonConstPL]
      return $ VProp (ConstVec constCols)

    ThetaJoin _ -> do
      cols1 <- unp c1 >>= fromDBV
      cols2 <- unp c2 >>= fromDBV
      let constCols = cols1 ++ cols2
      return $ VPropTriple (ConstVec constCols) CNA CNA

    NestJoin _ -> do
      cols1 <- unp c1 >>= fromDBV
      cols2 <- unp c2 >>= fromDBV
      let constCols = cols1 ++ cols2
      return $ VPropTriple (ConstVec constCols) CNA CNA

    SemiJoin _ -> do
      cols1 <- unp c1 >>= fromDBV
      return $ VPropPair (ConstVec cols1) CNA

    AntiJoin _ -> do
      cols1 <- unp c1 >>= fromDBV
      return $ VPropPair (ConstVec cols1) CNA

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

      let constCols = zipWith sameConst cols2 cols3
      return $ VPropTriple (ConstVec constCols) CNA CNA
