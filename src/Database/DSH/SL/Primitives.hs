{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- | Constructor functions for Segment Language primitives
module Database.DSH.SL.Primitives where

import qualified Data.List.NonEmpty             as N

import qualified Database.DSH.Common.Lang       as L
import           Database.DSH.Common.Nat
import qualified Database.DSH.Common.Type       as Ty
import           Database.DSH.Common.Vector
import           Database.DSH.Common.VectorLang

import           Database.DSH.Common.Impossible

import           Database.Algebra.Dag.Build
import           Database.Algebra.Dag.Common
import           Database.DSH.SL.Lang

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

slUnique :: SLDVec -> Build SL SLDVec
slUnique (SLDVec c) = vec (UnOp Unique c) dvec

slNumber :: SLDVec -> Build SL SLDVec
slNumber (SLDVec c) = vec (UnOp Number c) dvec

slGroup :: [Expr] -> SLDVec -> Build SL (SLDVec, SLDVec, SLSVec)
slGroup groupExprs (SLDVec c) = tripleVec (UnOp (Group groupExprs) c) dvec dvec svec

slSort :: [Expr] -> SLDVec -> Build SL (SLDVec, SLSVec)
slSort sortExprs (SLDVec c1) = pairVec (UnOp (Sort sortExprs) c1) dvec svec

slAggr :: AggrFun -> SLDVec -> Build SL SLDVec
slAggr aFun (SLDVec c) = vec (UnOp (Aggr (aFun N.:| [])) c) dvec

slAggrSeg :: AggrFun -> SLDVec -> SLDVec -> Build SL SLDVec
slAggrSeg aFun (SLDVec c1) (SLDVec c2) = vec (BinOp (AggrSeg aFun) c1 c2) dvec

slUnboxKey :: SLDVec -> Build SL SLKVec
slUnboxKey (SLDVec c) = vec (UnOp UnboxKey c) kvec

slReplicateNest :: SLDVec -> SLDVec -> Build SL (SLDVec, SLRVec)
slReplicateNest (SLDVec c1) (SLDVec c2) = pairVec (BinOp ReplicateNest c1 c2) dvec rvec

slReplicateVector :: SLDVec -> SLDVec -> Build SL (SLDVec, SLRVec)
slReplicateVector (SLDVec c1) (SLDVec c2) = pairVec (BinOp ReplicateVector c1 c2) dvec rvec

slReplicateScalar :: SLDVec -> SLDVec -> Build SL (SLDVec, SLRVec)
slReplicateScalar (SLDVec c1) (SLDVec c2) = pairVec (BinOp ReplicateScalar c1 c2) dvec rvec

slUnboxSng :: SLDVec -> SLDVec -> Build SL (SLDVec, SLKVec)
slUnboxSng (SLDVec c1) (SLDVec c2) = pairVec (BinOp UnboxSng c1 c2) dvec kvec

slAppSort :: SLSVec -> SLDVec -> Build SL (SLDVec, SLSVec)
slAppSort (SLSVec c1) (SLDVec c2) = pairVec (BinOp AppSort c1 c2) dvec svec

slAppFilter :: SLFVec -> SLDVec -> Build SL (SLDVec, SLFVec)
slAppFilter (SLFVec c1) (SLDVec c2) = pairVec (BinOp AppFilter c1 c2) dvec fvec

slAppKey :: SLKVec -> SLDVec -> Build SL (SLDVec, SLKVec)
slAppKey (SLKVec c1) (SLDVec c2) = pairVec (BinOp AppKey c1 c2) dvec kvec

slAppRep :: SLRVec -> SLDVec -> Build SL (SLDVec, SLRVec)
slAppRep (SLRVec c1) (SLDVec c2) = pairVec (BinOp AppRep c1 c2) dvec rvec

slNest :: SLDVec -> Build SL (SLDVec, SLDVec)
slNest (SLDVec c)= pairVec (UnOp Nest c) dvec dvec

slAppend :: SLDVec -> SLDVec -> Build SL (SLDVec, SLKVec, SLKVec)
slAppend (SLDVec c1) (SLDVec c2) = tripleVec (BinOp Append c1 c2) dvec kvec kvec

slSegment :: SLDVec -> Build SL SLDVec
slSegment (SLDVec c) = vec (UnOp Segment c) dvec

slUnsegment :: SLDVec -> Build SL SLDVec
slUnsegment (SLDVec c) = vec (UnOp Unsegment c) dvec

slCombine :: SLDVec -> SLDVec -> SLDVec -> Build SL (SLDVec, SLKVec, SLKVec)
slCombine (SLDVec c1) (SLDVec c2) (SLDVec c3) =
    tripleVec (TerOp Combine c1 c2 c3) dvec kvec kvec

slLit :: ([Ty.ScalarType], SegFrame, Segments) -> Build SL SLDVec
slLit i = vec (NullaryOp $ Lit i) dvec

slTableRef :: String -> L.BaseTableSchema -> Build SL SLDVec
slTableRef n schema = vec (NullaryOp $ TableRef (n, schema)) dvec

slUnExpr :: L.ScalarUnOp -> SLDVec -> Build SL SLDVec
slUnExpr o (SLDVec c) = vec (UnOp (Project [UnApp o (Column 1)]) c) dvec

slBinExpr :: L.ScalarBinOp -> SLDVec -> SLDVec -> Build SL SLDVec
slBinExpr o (SLDVec c1) (SLDVec c2) = do
    z <- insert $ BinOp Align c1 c2
    dvec $ insert $ UnOp (Project [BinApp o (Column 1) (Column 2)]) z

slSelect :: Expr -> SLDVec -> Build SL (SLDVec, SLFVec)
slSelect p (SLDVec c) = pairVec (UnOp (Select p) c) dvec fvec

slProject :: [Expr] -> SLDVec -> Build SL SLDVec
slProject projs (SLDVec c) = dvec $ insert $ UnOp (Project projs) c

slAlign :: SLDVec -> SLDVec -> Build SL SLDVec
slAlign (SLDVec c1) (SLDVec c2) = vec (BinOp Align c1 c2) dvec

slZip :: SLDVec -> SLDVec -> Build SL (SLDVec, SLKVec, SLKVec)
slZip (SLDVec c1) (SLDVec c2) =
    tripleVec (BinOp Zip c1 c2) dvec kvec kvec

slCartProduct :: SLDVec -> SLDVec -> Build SL (SLDVec, SLRVec, SLRVec)
slCartProduct (SLDVec c1) (SLDVec c2) =
    tripleVec (BinOp CartProduct c1 c2) dvec rvec rvec

slThetaJoin :: L.JoinPredicate L.ScalarExpr -> SLDVec -> SLDVec -> Build SL (SLDVec, SLRVec, SLRVec)
slThetaJoin joinPred (SLDVec c1) (SLDVec c2) =
    tripleVec (BinOp (ThetaJoin joinPred') c1 c2) dvec rvec rvec
  where
    joinPred' = toSLJoinPred joinPred

slNestJoin :: L.JoinPredicate L.ScalarExpr -> SLDVec -> SLDVec -> Build SL (SLDVec, SLRVec, SLRVec)
slNestJoin joinPred (SLDVec c1) (SLDVec c2) =
    tripleVec (BinOp (NestJoin joinPred') c1 c2) dvec rvec rvec
  where
    joinPred' = toSLJoinPred joinPred

slGroupJoin :: L.JoinPredicate L.ScalarExpr -> L.NE AggrFun -> SLDVec -> SLDVec -> Build SL SLDVec
slGroupJoin joinPred afuns (SLDVec c1) (SLDVec c2) =
    vec (BinOp (GroupJoin (joinPred', afuns)) c1 c2) dvec
  where
    joinPred' = toSLJoinPred joinPred

slSemiJoin :: L.JoinPredicate L.ScalarExpr -> SLDVec -> SLDVec -> Build SL (SLDVec, SLFVec)
slSemiJoin joinPred (SLDVec c1) (SLDVec c2) =
    pairVec (BinOp (SemiJoin joinPred') c1 c2) dvec fvec
  where
    joinPred' = toSLJoinPred joinPred

slAntiJoin :: L.JoinPredicate L.ScalarExpr -> SLDVec -> SLDVec -> Build SL (SLDVec, SLFVec)
slAntiJoin joinPred (SLDVec c1) (SLDVec c2) =
    pairVec (BinOp (AntiJoin joinPred') c1 c2) dvec fvec
  where
    joinPred' = toSLJoinPred joinPred

slReverse :: SLDVec -> Build SL (SLDVec, SLSVec)
slReverse (SLDVec c) = pairVec (UnOp Reverse c) dvec svec
