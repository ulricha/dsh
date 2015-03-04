{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Database.DSH.VL.Primitives where

import           Database.DSH.Common.Nat
import qualified Database.DSH.Common.Lang      as L
import qualified Database.DSH.Common.Type      as Ty
import           Database.DSH.Common.Vector

import           Database.DSH.Common.Impossible

import           Database.Algebra.Dag.Build
import           Database.Algebra.Dag.Common
import           Database.DSH.VL.Lang          hiding (DBCol)
import qualified Database.DSH.VL.Lang          as D

--------------------------------------------------------------------------------
-- Construct different types of vectors from algebraic nodes

type VecConst r v = Build VL AlgNode -> Build VL v

dvec :: VecConst r VLDVec
dvec = fmap VLDVec

pvec :: Build a AlgNode -> Build a PVec
pvec = fmap PVec

rvec :: Build a AlgNode -> Build a RVec
rvec = fmap RVec
     
--------------------------------------------------------------------------------
-- Insert VL operators and appropriate R1/R2/R3 nodes

vec :: VL -> VecConst r a -> Build VL a
vec op mkVec = mkVec $ insert op

pairVec :: VL -> VecConst r a -> VecConst r b -> Build VL (a, b)
pairVec op mkVec1 mkVec2 = do
    r <- insert op
    r1 <- mkVec1 $ insert $ UnOp R1 r
    r2 <- mkVec2 $ insert $ UnOp R2 r
    return (r1, r2)

tripleVec :: VL 
          -> VecConst r a 
          -> VecConst r b 
          -> VecConst r c 
          -> Build VL (a, b ,c)
tripleVec op mkVec1 mkVec2 mkVec3 = do
    r <- insert op
    r1 <- mkVec1 $ insert $ UnOp R1 r
    r2 <- mkVec2 $ insert $ UnOp R2 r
    r3 <- mkVec3 $ insert $ UnOp R3 r
    return (r1, r2, r3)

--------------------------------------------------------------------------------

mapSnd :: (b -> c) -> (a, b) -> (a, c)
mapSnd f (a, b) = (a, f b)

pVal :: L.Val -> VLVal
pVal (L.IntV i)    = VLInt i
pVal (L.BoolV b)   = VLBool b
pVal (L.StringV s) = VLString s
pVal (L.DoubleV d) = VLDouble d
pVal L.UnitV       = VLUnit
pVal _             = error "pVal: Not a supported value"

typeToScalarType :: Ty.Type -> ScalarType
typeToScalarType t = case t of
  Ty.IntT      -> D.Int
  Ty.BoolT     -> D.Bool
  Ty.StringT   -> D.String
  Ty.UnitT     -> D.Unit
  Ty.DoubleT   -> D.Double
  Ty.DecimalT  -> D.Decimal
  Ty.ListT _   -> $impossible
  Ty.TupleT _  -> $impossible

----------------------------------------------------------------------------------
-- Convert join expressions into regular VL expressions

-- | Determine the horizontal relational schema width of a type
recordWidth :: Ty.Type -> Int
recordWidth t =
    case t of
        Ty.IntT        -> 1
        Ty.BoolT       -> 1
        Ty.DoubleT     -> 1
        Ty.StringT     -> 1
        Ty.UnitT       -> 1
        Ty.DecimalT    -> 1
        Ty.TupleT ts   -> sum $ map recordWidth ts
        Ty.ListT _     -> 0

data ColExpr = Offset Int | Expr Expr

-- | If the child expressions are tuple operators which only give the
-- column offset, convert it into a proper expression first.
offsetExpr :: ColExpr -> Expr
offsetExpr (Offset o) = Column $ o + 1
offsetExpr (Expr e)   = e

addOffset :: Int -> ColExpr -> ColExpr
addOffset _ (Expr _)   = $impossible
addOffset i (Offset o) = Offset $ o + i

toGeneralBinOp :: L.JoinBinOp -> L.ScalarBinOp
toGeneralBinOp (L.JBNumOp o)    = L.SBNumOp o
toGeneralBinOp (L.JBStringOp o) = L.SBStringOp o

toGeneralUnOp :: L.JoinUnOp -> L.ScalarUnOp
toGeneralUnOp (L.JUNumOp o)  = L.SUNumOp o
toGeneralUnOp (L.JUCastOp o) = L.SUCastOp o
toGeneralUnOp (L.JUTextOp o) = L.SUTextOp o

toVLjoinConjunct :: L.JoinConjunct L.JoinExpr -> L.JoinConjunct Expr
toVLjoinConjunct (L.JoinConjunct e1 o e2) = 
    L.JoinConjunct (joinExpr e1) o (joinExpr e2)

toVLJoinPred :: L.JoinPredicate L.JoinExpr -> L.JoinPredicate Expr
toVLJoinPred (L.JoinPred cs) = L.JoinPred $ fmap toVLjoinConjunct cs

-- | Convert join expressions into VL expressions. The main challenge
-- here is to convert sequences of tuple accessors (fst/snd) into VL
-- column indices.
joinExpr :: L.JoinExpr -> Expr
joinExpr expr = offsetExpr $ aux expr
  where
    -- Construct expressions in a bottom-up way. For a given join
    -- expression, return the following:
    -- pair accessors   -> column offset in the flat relational representation
    -- scalar operation -> corresponding VL expression
    aux :: L.JoinExpr -> ColExpr
    -- FIXME VL joins should include join expressions!
    aux (L.JBinOp _ op e1 e2)  = Expr $ BinApp (toGeneralBinOp op)
                                               (offsetExpr $ aux e1)
                                               (offsetExpr $ aux e2)
    aux (L.JUnOp _ op e)       = Expr $ UnApp (toGeneralUnOp op) (offsetExpr $ aux e)
    aux (L.JTupElem _ i e)           =
        case Ty.typeOf e of
            -- Compute the record width of all preceding tuple elements in the type
            Ty.TupleT ts -> addOffset (sum $ map recordWidth $ take (tupleIndex i - 1) ts) (aux e)
            _            -> $impossible
    aux (L.JLit _ v)           = Expr $ Constant $ pVal v
    aux (L.JInput _)           = Offset 0


----------------------------------------------------------------------------------
-- DAG constructor functions for VL operators

vlUniqueS :: VLDVec -> Build VL VLDVec
vlUniqueS (VLDVec c) = vec (UnOp UniqueS c) dvec

vlNumber :: VLDVec -> Build VL VLDVec
vlNumber (VLDVec c) = vec (UnOp Number c) dvec

vlNumberS :: VLDVec -> Build VL VLDVec
vlNumberS (VLDVec c) = vec (UnOp NumberS c) dvec

vlGroupS :: [Expr] -> VLDVec -> Build VL (VLDVec, VLDVec, PVec)
vlGroupS groupExprs (VLDVec c) = tripleVec (UnOp (GroupS groupExprs) c) dvec dvec pvec

vlSortS :: [Expr] -> VLDVec -> Build VL (VLDVec, PVec)
vlSortS sortExprs (VLDVec c1) = pairVec (UnOp (SortS sortExprs) c1) dvec pvec

vlAggr :: AggrFun -> VLDVec -> Build VL VLDVec
vlAggr aFun (VLDVec c) = vec (UnOp (Aggr aFun) c) dvec

vlAggrS :: AggrFun -> VLDVec -> VLDVec -> Build VL VLDVec
vlAggrS aFun (VLDVec c1) (VLDVec c2) = vec (BinOp (AggrS aFun) c1 c2) dvec

vlUnboxRename :: VLDVec -> Build VL RVec
vlUnboxRename (VLDVec c) = vec (UnOp UnboxRename c) rvec

vlNestProduct :: VLDVec -> VLDVec -> Build VL (VLDVec, PVec, PVec)
vlNestProduct (VLDVec c1) (VLDVec c2) = tripleVec (BinOp NestProduct c1 c2) dvec pvec pvec

vlDistLift :: VLDVec -> VLDVec -> Build VL (VLDVec, PVec)
vlDistLift (VLDVec c1) (VLDVec c2) = pairVec (BinOp DistLift c1 c2) dvec pvec

vlPropRename :: RVec -> VLDVec -> Build VL VLDVec
vlPropRename (RVec c1) (VLDVec c2) = vec (BinOp PropRename c1 c2) dvec

vlUnboxNested :: RVec -> VLDVec -> Build VL (VLDVec, RVec)
vlUnboxNested (RVec c1) (VLDVec c2) = pairVec (BinOp UnboxNested c1 c2) dvec rvec

vlUnboxScalar :: VLDVec -> VLDVec -> Build VL VLDVec
vlUnboxScalar (VLDVec c1) (VLDVec c2) = vec (BinOp UnboxScalar c1 c2) dvec

vlPropFilter :: RVec -> VLDVec -> Build VL (VLDVec, RVec)
vlPropFilter (RVec c1) (VLDVec c2) = pairVec (BinOp PropFilter c1 c2) dvec rvec

vlPropReorder :: PVec -> VLDVec -> Build VL (VLDVec, PVec)
vlPropReorder (PVec c1) (VLDVec c2) = pairVec (BinOp PropReorder c1 c2) dvec pvec

vlSingletonDescr :: Build VL VLDVec
vlSingletonDescr = vec (NullaryOp SingletonDescr) dvec

vlAppend :: VLDVec -> VLDVec -> Build VL (VLDVec, RVec, RVec)
vlAppend (VLDVec c1) (VLDVec c2) = tripleVec (BinOp Append c1 c2) dvec rvec rvec

vlAppendS :: VLDVec -> VLDVec -> Build VL (VLDVec, RVec, RVec)
vlAppendS (VLDVec c1) (VLDVec c2) = tripleVec (BinOp AppendS c1 c2) dvec rvec rvec

vlSegment :: VLDVec -> Build VL VLDVec
vlSegment (VLDVec c) = vec (UnOp Segment c) dvec

vlUnsegment :: VLDVec -> Build VL VLDVec
vlUnsegment (VLDVec c) = vec (UnOp Unsegment c) dvec

vlCombine :: VLDVec -> VLDVec -> VLDVec -> Build VL (VLDVec, RVec, RVec)
vlCombine (VLDVec c1) (VLDVec c2) (VLDVec c3) = 
    tripleVec (TerOp Combine c1 c2 c3) dvec rvec rvec

vlLit :: L.Emptiness -> [Ty.Type] -> [[VLVal]] -> Build VL VLDVec
vlLit em tys vals = vec (NullaryOp $ Lit (em, map typeToScalarType tys, vals)) dvec

vlTableRef :: String -> [VLColumn] -> L.TableHints -> Build VL VLDVec
vlTableRef n tys hs = vec (NullaryOp $ TableRef (n, tys, hs)) dvec

vlUnExpr :: L.ScalarUnOp -> VLDVec -> Build VL VLDVec
vlUnExpr o (VLDVec c) = vec (UnOp (Project [UnApp o (Column 1)]) c) dvec

vlBinExpr :: L.ScalarBinOp -> VLDVec -> VLDVec -> Build VL VLDVec
vlBinExpr o (VLDVec c1) (VLDVec c2) = do
    z <- insert $ BinOp Align c1 c2
    r <- dvec $ insert $ UnOp (Project [BinApp o (Column 1) (Column 2)]) z
    return r

vlSelect :: Expr -> VLDVec -> Build VL (VLDVec, RVec)
vlSelect p (VLDVec c) = pairVec (UnOp (Select p) c) dvec rvec

vlSelectPos :: VLDVec -> L.ScalarBinOp -> VLDVec -> Build VL (VLDVec, RVec, RVec)
vlSelectPos (VLDVec c1) op (VLDVec c2) = tripleVec (BinOp (SelectPos op) c1 c2) dvec rvec rvec

vlSelectPos1 :: VLDVec -> L.ScalarBinOp -> Int -> Build VL (VLDVec, RVec, RVec)
vlSelectPos1 (VLDVec c1) op posConst = 
    tripleVec (UnOp (SelectPos1 (op, posConst)) c1) dvec rvec rvec

vlSelectPosS :: VLDVec -> L.ScalarBinOp -> VLDVec -> Build VL (VLDVec, RVec, RVec)
vlSelectPosS (VLDVec c1) op (VLDVec c2) = do
    tripleVec (BinOp (SelectPosS op) c1 c2) dvec rvec rvec

vlSelectPos1S :: VLDVec -> L.ScalarBinOp -> Int -> Build VL (VLDVec, RVec, RVec)
vlSelectPos1S (VLDVec c1) op posConst = 
    tripleVec (UnOp (SelectPos1S (op, posConst)) c1) dvec rvec rvec

vlProject :: [Expr] -> VLDVec -> Build VL VLDVec
vlProject projs (VLDVec c) = dvec $ insert $ UnOp (Project projs) c

vlZip :: VLDVec -> VLDVec -> Build VL VLDVec
vlZip (VLDVec c1) (VLDVec c2) = vec (BinOp Zip c1 c2) dvec

vlAlign :: VLDVec -> VLDVec -> Build VL VLDVec
vlAlign (VLDVec c1) (VLDVec c2) = vec (BinOp Align c1 c2) dvec

vlZipS :: VLDVec -> VLDVec -> Build VL (VLDVec, RVec, RVec)
vlZipS (VLDVec c1) (VLDVec c2) =
    tripleVec (BinOp ZipS c1 c2) dvec rvec rvec

vlCartProduct :: VLDVec -> VLDVec -> Build VL (VLDVec, PVec, PVec)
vlCartProduct (VLDVec c1) (VLDVec c2) =
    tripleVec (BinOp CartProduct c1 c2) dvec pvec pvec

vlCartProductS :: VLDVec -> VLDVec -> Build VL (VLDVec, PVec, PVec)
vlCartProductS (VLDVec c1) (VLDVec c2) =
    tripleVec (BinOp CartProductS c1 c2) dvec pvec pvec

vlThetaJoin :: L.JoinPredicate L.JoinExpr -> VLDVec -> VLDVec -> Build VL (VLDVec, PVec, PVec)
vlThetaJoin joinPred (VLDVec c1) (VLDVec c2) =
    tripleVec (BinOp (ThetaJoin joinPred') c1 c2) dvec pvec pvec
  where
    joinPred' = toVLJoinPred joinPred

vlNestJoin :: L.JoinPredicate L.JoinExpr -> VLDVec -> VLDVec -> Build VL (VLDVec, PVec, PVec)
vlNestJoin joinPred (VLDVec c1) (VLDVec c2) =
    tripleVec (BinOp (NestJoin joinPred') c1 c2) dvec pvec pvec
  where
    joinPred' = toVLJoinPred joinPred

vlThetaJoinS :: L.JoinPredicate L.JoinExpr -> VLDVec -> VLDVec -> Build VL (VLDVec, PVec, PVec)
vlThetaJoinS joinPred (VLDVec c1) (VLDVec c2) =
    tripleVec (BinOp (ThetaJoinS joinPred') c1 c2) dvec pvec pvec
  where
    joinPred' = toVLJoinPred joinPred

vlNestJoinS :: L.JoinPredicate L.JoinExpr -> VLDVec -> VLDVec -> Build VL (VLDVec, PVec)
vlNestJoinS joinPred (VLDVec c1) (VLDVec c2) =
    pairVec (BinOp (NestJoinS joinPred') c1 c2) dvec pvec
  where
    joinPred' = toVLJoinPred joinPred

vlNestProductS :: VLDVec -> VLDVec -> Build VL (VLDVec, PVec)
vlNestProductS (VLDVec c1) (VLDVec c2) = do
    pairVec (BinOp NestProductS c1 c2) dvec pvec

vlSemiJoin :: L.JoinPredicate L.JoinExpr -> VLDVec -> VLDVec -> Build VL (VLDVec, RVec)
vlSemiJoin joinPred (VLDVec c1) (VLDVec c2) = do
    pairVec (BinOp (SemiJoin joinPred') c1 c2) dvec rvec
  where
    joinPred' = toVLJoinPred joinPred

vlSemiJoinS :: L.JoinPredicate L.JoinExpr -> VLDVec -> VLDVec -> Build VL (VLDVec, RVec)
vlSemiJoinS joinPred (VLDVec c1) (VLDVec c2) = do
    pairVec (BinOp (SemiJoinS joinPred') c1 c2) dvec rvec
  where
    joinPred' = toVLJoinPred joinPred

vlAntiJoin :: L.JoinPredicate L.JoinExpr -> VLDVec -> VLDVec -> Build VL (VLDVec, RVec)
vlAntiJoin joinPred (VLDVec c1) (VLDVec c2) = do
    pairVec (BinOp (AntiJoin joinPred') c1 c2) dvec rvec
  where
    joinPred' = toVLJoinPred joinPred

vlAntiJoinS :: L.JoinPredicate L.JoinExpr -> VLDVec -> VLDVec -> Build VL (VLDVec, RVec)
vlAntiJoinS joinPred (VLDVec c1) (VLDVec c2) = do
    pairVec (BinOp (AntiJoinS joinPred') c1 c2) dvec rvec
  where
    joinPred' = toVLJoinPred joinPred

vlReverse :: VLDVec -> Build VL (VLDVec, PVec)
vlReverse (VLDVec c) = pairVec (UnOp Reverse c) dvec pvec

vlReverseS :: VLDVec -> Build VL (VLDVec, PVec)
vlReverseS (VLDVec c) = pairVec (UnOp ReverseS c) dvec pvec

vlTranspose :: VLDVec -> Build VL (VLDVec, VLDVec)
vlTranspose (VLDVec c) = pairVec (UnOp Transpose c) dvec dvec

vlTransposeS :: VLDVec -> VLDVec -> Build VL (VLDVec, VLDVec)
vlTransposeS (VLDVec c1) (VLDVec c2) = do
    pairVec (BinOp TransposeS c1 c2) dvec dvec

vlReshape :: Integer -> VLDVec -> Build VL (VLDVec, VLDVec)
vlReshape n (VLDVec c) = do
    pairVec (UnOp (Reshape n) c) dvec dvec

vlReshapeS :: Integer -> VLDVec -> Build VL (VLDVec, VLDVec)
vlReshapeS n (VLDVec c) = do
    pairVec (UnOp (ReshapeS n) c) dvec dvec
