{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- | Constructor functions for Segment Language primitives
module Database.DSH.SL.Primitives where

import qualified Data.List.NonEmpty as N

import           Database.DSH.Common.Nat
import qualified Database.DSH.Common.Lang      as L
import qualified Database.DSH.Common.Type      as Ty
import           Database.DSH.Common.Vector

import           Database.DSH.Common.Impossible

import           Database.Algebra.Dag.Build
import           Database.Algebra.Dag.Common
import           Database.DSH.SL.Lang          hiding (DBCol)

--------------------------------------------------------------------------------
-- Construct different types of vectors from algebraic nodes

type VecConst r v = Build SL AlgNode -> Build SL v

dvec :: VecConst r SLDVec
dvec = fmap SLDVec

rvec :: Build a AlgNode -> Build a SLRVec
rvec = fmap SLRVec

kvec :: Build a AlgNode -> Build a SLKVec
kvec = fmap SLKVec

svec :: Build a AlgNode -> Build a SLSVec
svec = fmap SLSVec

fvec :: Build a AlgNode -> Build a SLFVec
fvec = fmap SLFVec

--------------------------------------------------------------------------------
-- Insert SL operators and appropriate R1/R2/R3 nodes

vec :: SL -> VecConst r a -> Build SL a
vec op mkVec = mkVec $ insert op

pairVec :: SL -> VecConst r a -> VecConst r b -> Build SL (a, b)
pairVec op mkVec1 mkVec2 = do
    r <- insert op
    r1 <- mkVec1 $ insert $ UnOp R1 r
    r2 <- mkVec2 $ insert $ UnOp R2 r
    return (r1, r2)

tripleVec :: SL
          -> VecConst r a
          -> VecConst r b
          -> VecConst r c
          -> Build SL (a, b ,c)
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
-- Convert join expressions into regular SL expressions

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

toSLjoinConjunct :: L.JoinConjunct L.ScalarExpr -> L.JoinConjunct Expr
toSLjoinConjunct (L.JoinConjunct e1 o e2) =
    L.JoinConjunct (scalarExpr e1) o (scalarExpr e2)

toSLJoinPred :: L.JoinPredicate L.ScalarExpr -> L.JoinPredicate Expr
toSLJoinPred (L.JoinPred cs) = L.JoinPred $ fmap toSLjoinConjunct cs

-- | Convert join expressions into SL expressions. The main challenge
-- here is to convert sequences of tuple accessors (fst/snd) into SL
-- column indices.
scalarExpr :: L.ScalarExpr -> Expr
scalarExpr expr = offsetExpr $ aux expr
  where
    -- Construct expressions in a bottom-up way. For a given join
    -- expression, return the following:
    -- pair accessors   -> column offset in the flat relational representation
    -- scalar operation -> corresponding SL expression
    aux :: L.ScalarExpr -> ColExpr
    -- FIXME SL joins should include join expressions!
    aux (L.JBinOp op e1 e2)  = Expr $ BinApp op
                                             (offsetExpr $ aux e1)
                                             (offsetExpr $ aux e2)
    aux (L.JUnOp op e)       = Expr $ UnApp op (offsetExpr $ aux e)
    aux (L.JTupElem i e)     =
        case Ty.typeOf e of
            -- Compute the record width of all preceding tuple elements in the type
            Ty.TupleT ts -> addOffset (sum $ map recordWidth $ take (tupleIndex i - 1) ts) (aux e)
            _            -> $impossible
    aux (L.JLit _ v)         = Expr $ Constant $ pVal v
    aux (L.JInput _)         = Offset 0


----------------------------------------------------------------------------------
-- DAG constructor functions for SL operators

vlUnique :: SLDVec -> Build SL SLDVec
vlUnique (SLDVec c) = vec (UnOp Unique c) dvec

vlNumber :: SLDVec -> Build SL SLDVec
vlNumber (SLDVec c) = vec (UnOp Number c) dvec

vlGroup :: [Expr] -> SLDVec -> Build SL (SLDVec, SLDVec, SLSVec)
vlGroup groupExprs (SLDVec c) = tripleVec (UnOp (Group groupExprs) c) dvec dvec svec

vlSort :: [Expr] -> SLDVec -> Build SL (SLDVec, SLSVec)
vlSort sortExprs (SLDVec c1) = pairVec (UnOp (Sort sortExprs) c1) dvec svec

vlAggr :: AggrFun -> SLDVec -> Build SL SLDVec
vlAggr aFun (SLDVec c) = vec (UnOp (Aggr (aFun N.:| [])) c) dvec

vlAggrSeg :: AggrFun -> SLDVec -> SLDVec -> Build SL SLDVec
vlAggrSeg aFun (SLDVec c1) (SLDVec c2) = vec (BinOp (AggrSeg aFun) c1 c2) dvec

vlUnboxKey :: SLDVec -> Build SL SLKVec
vlUnboxKey (SLDVec c) = vec (UnOp UnboxKey c) kvec

vlReplicateNest :: SLDVec -> SLDVec -> Build SL (SLDVec, SLRVec)
vlReplicateNest (SLDVec c1) (SLDVec c2) = pairVec (BinOp ReplicateNest c1 c2) dvec rvec

vlReplicateVector :: SLDVec -> SLDVec -> Build SL (SLDVec, SLRVec)
vlReplicateVector (SLDVec c1) (SLDVec c2) = pairVec (BinOp ReplicateVector c1 c2) dvec rvec

vlReplicateScalar :: SLDVec -> SLDVec -> Build SL (SLDVec, SLRVec)
vlReplicateScalar (SLDVec c1) (SLDVec c2) = pairVec (BinOp ReplicateScalar c1 c2) dvec rvec

vlUnboxSng :: SLDVec -> SLDVec -> Build SL (SLDVec, SLKVec)
vlUnboxSng (SLDVec c1) (SLDVec c2) = pairVec (BinOp UnboxSng c1 c2) dvec kvec

vlAppSort :: SLSVec -> SLDVec -> Build SL (SLDVec, SLSVec)
vlAppSort (SLSVec c1) (SLDVec c2) = pairVec (BinOp AppSort c1 c2) dvec svec

vlAppFilter :: SLFVec -> SLDVec -> Build SL (SLDVec, SLFVec)
vlAppFilter (SLFVec c1) (SLDVec c2) = pairVec (BinOp AppFilter c1 c2) dvec fvec

vlAppKey :: SLKVec -> SLDVec -> Build SL (SLDVec, SLKVec)
vlAppKey (SLKVec c1) (SLDVec c2) = pairVec (BinOp AppKey c1 c2) dvec kvec

vlAppRep :: SLRVec -> SLDVec -> Build SL (SLDVec, SLRVec)
vlAppRep (SLRVec c1) (SLDVec c2) = pairVec (BinOp AppRep c1 c2) dvec rvec

vlNest :: SLDVec -> Build SL (SLDVec, SLDVec)
vlNest (SLDVec c)= pairVec (UnOp Nest c) dvec dvec

vlAppend :: SLDVec -> SLDVec -> Build SL (SLDVec, SLKVec, SLKVec)
vlAppend (SLDVec c1) (SLDVec c2) = tripleVec (BinOp Append c1 c2) dvec kvec kvec

vlSegment :: SLDVec -> Build SL SLDVec
vlSegment (SLDVec c) = vec (UnOp Segment c) dvec

vlUnsegment :: SLDVec -> Build SL SLDVec
vlUnsegment (SLDVec c) = vec (UnOp Unsegment c) dvec

vlCombine :: SLDVec -> SLDVec -> SLDVec -> Build SL (SLDVec, SLKVec, SLKVec)
vlCombine (SLDVec c1) (SLDVec c2) (SLDVec c3) =
    tripleVec (TerOp Combine c1 c2 c3) dvec kvec kvec

vlLit :: ([Ty.ScalarType], SegFrame, Segments) -> Build SL SLDVec
vlLit i = vec (NullaryOp $ Lit i) dvec

vlTableRef :: String -> L.BaseTableSchema -> Build SL SLDVec
vlTableRef n schema = vec (NullaryOp $ TableRef (n, schema)) dvec

vlUnExpr :: L.ScalarUnOp -> SLDVec -> Build SL SLDVec
vlUnExpr o (SLDVec c) = vec (UnOp (Project [UnApp o (Column 1)]) c) dvec

vlBinExpr :: L.ScalarBinOp -> SLDVec -> SLDVec -> Build SL SLDVec
vlBinExpr o (SLDVec c1) (SLDVec c2) = do
    z <- insert $ BinOp Align c1 c2
    dvec $ insert $ UnOp (Project [BinApp o (Column 1) (Column 2)]) z

vlSelect :: Expr -> SLDVec -> Build SL (SLDVec, SLFVec)
vlSelect p (SLDVec c) = pairVec (UnOp (Select p) c) dvec fvec

vlProject :: [Expr] -> SLDVec -> Build SL SLDVec
vlProject projs (SLDVec c) = dvec $ insert $ UnOp (Project projs) c

vlAlign :: SLDVec -> SLDVec -> Build SL SLDVec
vlAlign (SLDVec c1) (SLDVec c2) = vec (BinOp Align c1 c2) dvec

vlZip :: SLDVec -> SLDVec -> Build SL (SLDVec, SLKVec, SLKVec)
vlZip (SLDVec c1) (SLDVec c2) =
    tripleVec (BinOp Zip c1 c2) dvec kvec kvec

vlCartProduct :: SLDVec -> SLDVec -> Build SL (SLDVec, SLRVec, SLRVec)
vlCartProduct (SLDVec c1) (SLDVec c2) =
    tripleVec (BinOp CartProduct c1 c2) dvec rvec rvec

vlThetaJoin :: L.JoinPredicate L.ScalarExpr -> SLDVec -> SLDVec -> Build SL (SLDVec, SLRVec, SLRVec)
vlThetaJoin joinPred (SLDVec c1) (SLDVec c2) =
    tripleVec (BinOp (ThetaJoin joinPred') c1 c2) dvec rvec rvec
  where
    joinPred' = toSLJoinPred joinPred

vlNestJoin :: L.JoinPredicate L.ScalarExpr -> SLDVec -> SLDVec -> Build SL (SLDVec, SLRVec, SLRVec)
vlNestJoin joinPred (SLDVec c1) (SLDVec c2) =
    tripleVec (BinOp (NestJoin joinPred') c1 c2) dvec rvec rvec
  where
    joinPred' = toSLJoinPred joinPred

vlGroupJoin :: L.JoinPredicate L.ScalarExpr -> L.NE AggrFun -> SLDVec -> SLDVec -> Build SL SLDVec
vlGroupJoin joinPred afuns (SLDVec c1) (SLDVec c2) =
    vec (BinOp (GroupJoin (joinPred', afuns)) c1 c2) dvec
  where
    joinPred' = toSLJoinPred joinPred

vlSemiJoin :: L.JoinPredicate L.ScalarExpr -> SLDVec -> SLDVec -> Build SL (SLDVec, SLFVec)
vlSemiJoin joinPred (SLDVec c1) (SLDVec c2) =
    pairVec (BinOp (SemiJoin joinPred') c1 c2) dvec fvec
  where
    joinPred' = toSLJoinPred joinPred

vlAntiJoin :: L.JoinPredicate L.ScalarExpr -> SLDVec -> SLDVec -> Build SL (SLDVec, SLFVec)
vlAntiJoin joinPred (SLDVec c1) (SLDVec c2) =
    pairVec (BinOp (AntiJoin joinPred') c1 c2) dvec fvec
  where
    joinPred' = toSLJoinPred joinPred

vlReverse :: SLDVec -> Build SL (SLDVec, SLSVec)
vlReverse (SLDVec c) = pairVec (UnOp Reverse c) dvec svec
