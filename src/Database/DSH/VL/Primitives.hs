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

--------------------------------------------------------------------------------
-- Construct different types of vectors from algebraic nodes

type VecConst r v = Build VL AlgNode -> Build VL v

dvec :: VecConst r VLDVec
dvec = fmap VLDVec

rvec :: Build a AlgNode -> Build a VLRVec
rvec = fmap VLRVec

kvec :: Build a AlgNode -> Build a VLKVec
kvec = fmap VLKVec

svec :: Build a AlgNode -> Build a VLSVec
svec = fmap VLSVec

fvec :: Build a AlgNode -> Build a VLFVec
fvec = fmap VLFVec

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

pVal :: L.Val -> L.ScalarVal
pVal (L.ScalarV v) = v
pVal L.ListV{}     = $impossible
pVal L.TupleV{}    = $impossible

typeToScalarType :: Ty.Type -> Ty.ScalarType
typeToScalarType Ty.ListT{}     = $impossible
typeToScalarType Ty.TupleT{}    = $impossible
typeToScalarType (Ty.ScalarT t) = t

----------------------------------------------------------------------------------
-- Convert join expressions into regular VL expressions

-- | Determine the horizontal relational schema width of a type
recordWidth :: Ty.Type -> Int
recordWidth t =
    case t of
        Ty.ScalarT _   -> 1
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

vlUnique :: VLDVec -> Build VL VLDVec
vlUnique (VLDVec c) = vec (UnOp Unique c) dvec

vlUniqueS :: VLDVec -> Build VL VLDVec
vlUniqueS (VLDVec c) = vec (UnOp UniqueS c) dvec

vlNumber :: VLDVec -> Build VL VLDVec
vlNumber (VLDVec c) = vec (UnOp Number c) dvec

vlNumberS :: VLDVec -> Build VL VLDVec
vlNumberS (VLDVec c) = vec (UnOp NumberS c) dvec

vlGroup :: [Expr] -> VLDVec -> Build VL (VLDVec, VLDVec, VLSVec)
vlGroup groupExprs (VLDVec c) = tripleVec (UnOp (Group groupExprs) c) dvec dvec svec

vlGroupS :: [Expr] -> VLDVec -> Build VL (VLDVec, VLDVec, VLSVec)
vlGroupS groupExprs (VLDVec c) = tripleVec (UnOp (GroupS groupExprs) c) dvec dvec svec

vlSort :: [Expr] -> VLDVec -> Build VL (VLDVec, VLSVec)
vlSort sortExprs (VLDVec c1) = pairVec (UnOp (Sort sortExprs) c1) dvec svec

vlSortS :: [Expr] -> VLDVec -> Build VL (VLDVec, VLSVec)
vlSortS sortExprs (VLDVec c1) = pairVec (UnOp (SortS sortExprs) c1) dvec svec

vlAggr :: AggrFun -> VLDVec -> Build VL VLDVec
vlAggr aFun (VLDVec c) = vec (UnOp (Aggr aFun) c) dvec

vlAggrS :: AggrFun -> VLDVec -> VLDVec -> Build VL VLDVec
vlAggrS aFun (VLDVec c1) (VLDVec c2) = vec (BinOp (AggrS aFun) c1 c2) dvec

vlUnboxKey :: VLDVec -> Build VL VLKVec
vlUnboxKey (VLDVec c) = vec (UnOp UnboxKey c) kvec

vlNestProduct :: VLDVec -> VLDVec -> Build VL (VLDVec, VLRVec, VLRVec)
vlNestProduct (VLDVec c1) (VLDVec c2) = tripleVec (BinOp NestProduct c1 c2) dvec rvec rvec

vlDistLift :: VLDVec -> VLDVec -> Build VL (VLDVec, VLRVec)
vlDistLift (VLDVec c1) (VLDVec c2) = pairVec (BinOp DistLift c1 c2) dvec rvec

vlUnboxScalar :: VLDVec -> VLDVec -> Build VL VLDVec
vlUnboxScalar (VLDVec c1) (VLDVec c2) = vec (BinOp UnboxScalar c1 c2) dvec

vlAppSort :: VLSVec -> VLDVec -> Build VL (VLDVec, VLSVec)
vlAppSort (VLSVec c1) (VLDVec c2) = pairVec (BinOp AppSort c1 c2) dvec svec

vlAppFilter :: VLFVec -> VLDVec -> Build VL (VLDVec, VLFVec)
vlAppFilter (VLFVec c1) (VLDVec c2) = pairVec (BinOp AppFilter c1 c2) dvec fvec

vlAppKey :: VLKVec -> VLDVec -> Build VL (VLDVec, VLKVec)
vlAppKey (VLKVec c1) (VLDVec c2) = pairVec (BinOp AppKey c1 c2) dvec kvec

vlAppRep :: VLRVec -> VLDVec -> Build VL (VLDVec, VLRVec)
vlAppRep (VLRVec c1) (VLDVec c2) = pairVec (BinOp AppRep c1 c2) dvec rvec

vlSingletonDescr :: Build VL VLDVec
vlSingletonDescr = vec (NullaryOp SingletonDescr) dvec

vlAppend :: VLDVec -> VLDVec -> Build VL (VLDVec, VLKVec, VLKVec)
vlAppend (VLDVec c1) (VLDVec c2) = tripleVec (BinOp Append c1 c2) dvec kvec kvec

vlAppendS :: VLDVec -> VLDVec -> Build VL (VLDVec, VLKVec, VLKVec)
vlAppendS (VLDVec c1) (VLDVec c2) = tripleVec (BinOp AppendS c1 c2) dvec kvec kvec

vlSegment :: VLDVec -> Build VL VLDVec
vlSegment (VLDVec c) = vec (UnOp Segment c) dvec

vlUnsegment :: VLDVec -> Build VL VLDVec
vlUnsegment (VLDVec c) = vec (UnOp Unsegment c) dvec

vlCombine :: VLDVec -> VLDVec -> VLDVec -> Build VL (VLDVec, VLKVec, VLKVec)
vlCombine (VLDVec c1) (VLDVec c2) (VLDVec c3) =
    tripleVec (TerOp Combine c1 c2 c3) dvec kvec kvec

vlLit :: L.Emptiness -> [Ty.Type] -> [[L.ScalarVal]] -> Build VL VLDVec
vlLit em tys vals = vec (NullaryOp $ Lit (em, map typeToScalarType tys, vals)) dvec

vlTableRef :: String -> L.BaseTableSchema -> Build VL VLDVec
vlTableRef n schema = vec (NullaryOp $ TableRef (n, schema)) dvec

vlUnExpr :: L.ScalarUnOp -> VLDVec -> Build VL VLDVec
vlUnExpr o (VLDVec c) = vec (UnOp (Project [UnApp o (Column 1)]) c) dvec

vlBinExpr :: L.ScalarBinOp -> VLDVec -> VLDVec -> Build VL VLDVec
vlBinExpr o (VLDVec c1) (VLDVec c2) = do
    z <- insert $ BinOp Align c1 c2
    r <- dvec $ insert $ UnOp (Project [BinApp o (Column 1) (Column 2)]) z
    return r

vlSelect :: Expr -> VLDVec -> Build VL (VLDVec, VLFVec)
vlSelect p (VLDVec c) = pairVec (UnOp (Select p) c) dvec fvec

vlProject :: [Expr] -> VLDVec -> Build VL VLDVec
vlProject projs (VLDVec c) = dvec $ insert $ UnOp (Project projs) c

vlZip :: VLDVec -> VLDVec -> Build VL (VLDVec, VLKVec, VLKVec)
vlZip (VLDVec c1) (VLDVec c2) = tripleVec (BinOp Zip c1 c2) dvec kvec kvec

vlAlign :: VLDVec -> VLDVec -> Build VL VLDVec
vlAlign (VLDVec c1) (VLDVec c2) = vec (BinOp Align c1 c2) dvec

vlZipS :: VLDVec -> VLDVec -> Build VL (VLDVec, VLKVec, VLKVec)
vlZipS (VLDVec c1) (VLDVec c2) =
    tripleVec (BinOp ZipS c1 c2) dvec kvec kvec

vlCartProduct :: VLDVec -> VLDVec -> Build VL (VLDVec, VLRVec, VLRVec)
vlCartProduct (VLDVec c1) (VLDVec c2) =
    tripleVec (BinOp CartProduct c1 c2) dvec rvec rvec

vlCartProductS :: VLDVec -> VLDVec -> Build VL (VLDVec, VLRVec, VLRVec)
vlCartProductS (VLDVec c1) (VLDVec c2) =
    tripleVec (BinOp CartProductS c1 c2) dvec rvec rvec

vlThetaJoin :: L.JoinPredicate L.JoinExpr -> VLDVec -> VLDVec -> Build VL (VLDVec, VLRVec, VLRVec)
vlThetaJoin joinPred (VLDVec c1) (VLDVec c2) =
    tripleVec (BinOp (ThetaJoin joinPred') c1 c2) dvec rvec rvec
  where
    joinPred' = toVLJoinPred joinPred

vlNestJoin :: L.JoinPredicate L.JoinExpr -> VLDVec -> VLDVec -> Build VL (VLDVec, VLRVec, VLRVec)
vlNestJoin joinPred (VLDVec c1) (VLDVec c2) =
    tripleVec (BinOp (NestJoin joinPred') c1 c2) dvec rvec rvec
  where
    joinPred' = toVLJoinPred joinPred

vlThetaJoinS :: L.JoinPredicate L.JoinExpr -> VLDVec -> VLDVec -> Build VL (VLDVec, VLRVec, VLRVec)
vlThetaJoinS joinPred (VLDVec c1) (VLDVec c2) =
    tripleVec (BinOp (ThetaJoinS joinPred') c1 c2) dvec rvec rvec
  where
    joinPred' = toVLJoinPred joinPred

vlNestJoinS :: L.JoinPredicate L.JoinExpr -> VLDVec -> VLDVec -> Build VL (VLDVec, VLRVec, VLRVec)
vlNestJoinS joinPred (VLDVec c1) (VLDVec c2) =
    tripleVec (BinOp (NestJoinS joinPred') c1 c2) dvec rvec rvec
  where
    joinPred' = toVLJoinPred joinPred

vlNestProductS :: VLDVec -> VLDVec -> Build VL (VLDVec, VLRVec, VLRVec)
vlNestProductS (VLDVec c1) (VLDVec c2) = do
    tripleVec (BinOp NestProductS c1 c2) dvec rvec rvec

vlSemiJoin :: L.JoinPredicate L.JoinExpr -> VLDVec -> VLDVec -> Build VL (VLDVec, VLFVec)
vlSemiJoin joinPred (VLDVec c1) (VLDVec c2) = do
    pairVec (BinOp (SemiJoin joinPred') c1 c2) dvec fvec
  where
    joinPred' = toVLJoinPred joinPred

vlSemiJoinS :: L.JoinPredicate L.JoinExpr -> VLDVec -> VLDVec -> Build VL (VLDVec, VLFVec)
vlSemiJoinS joinPred (VLDVec c1) (VLDVec c2) = do
    pairVec (BinOp (SemiJoinS joinPred') c1 c2) dvec fvec
  where
    joinPred' = toVLJoinPred joinPred

vlAntiJoin :: L.JoinPredicate L.JoinExpr -> VLDVec -> VLDVec -> Build VL (VLDVec, VLFVec)
vlAntiJoin joinPred (VLDVec c1) (VLDVec c2) = do
    pairVec (BinOp (AntiJoin joinPred') c1 c2) dvec fvec
  where
    joinPred' = toVLJoinPred joinPred

vlAntiJoinS :: L.JoinPredicate L.JoinExpr -> VLDVec -> VLDVec -> Build VL (VLDVec, VLFVec)
vlAntiJoinS joinPred (VLDVec c1) (VLDVec c2) = do
    pairVec (BinOp (AntiJoinS joinPred') c1 c2) dvec fvec
  where
    joinPred' = toVLJoinPred joinPred

vlReverse :: VLDVec -> Build VL (VLDVec, VLSVec)
vlReverse (VLDVec c) = pairVec (UnOp Reverse c) dvec svec

vlReverseS :: VLDVec -> Build VL (VLDVec, VLSVec)
vlReverseS (VLDVec c) = pairVec (UnOp ReverseS c) dvec svec

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
