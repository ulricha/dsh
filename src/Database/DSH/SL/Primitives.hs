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

dvec :: VecConst r DVec
dvec = fmap DVec

rvec :: Build a AlgNode -> Build a RVec
rvec = fmap RVec

kvec :: Build a AlgNode -> Build a KVec
kvec = fmap KVec

svec :: Build a AlgNode -> Build a SVec
svec = fmap SVec

fvec :: Build a AlgNode -> Build a FVec
fvec = fmap FVec

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

typeToScalarType :: Ty.Type -> Ty.ScalarType
typeToScalarType Ty.ListT{}     = $impossible
typeToScalarType Ty.TupleT{}    = $impossible
typeToScalarType (Ty.ScalarT t) = t

----------------------------------------------------------------------------------
-- DAG constructor functions for SL operators

slUnique :: DVec -> Build SL DVec
slUnique (DVec c) = vec (UnOp Unique c) dvec

slNumber :: DVec -> Build SL DVec
slNumber (DVec c) = vec (UnOp Number c) dvec

slGroup :: [Expr] -> DVec -> Build SL (DVec, DVec, SVec)
slGroup groupExprs (DVec c) = tripleVec (UnOp (Group groupExprs) c) dvec dvec svec

slSort :: [Expr] -> DVec -> Build SL (DVec, SVec)
slSort sortExprs (DVec c1) = pairVec (UnOp (Sort sortExprs) c1) dvec svec

slAggr :: AggrFun -> DVec -> Build SL DVec
slAggr aFun (DVec c) = vec (UnOp (Aggr (aFun N.:| [])) c) dvec

slAggrSeg :: AggrFun -> DVec -> DVec -> Build SL DVec
slAggrSeg aFun (DVec c1) (DVec c2) = vec (BinOp (AggrSeg aFun) c1 c2) dvec

slUnboxKey :: DVec -> Build SL KVec
slUnboxKey (DVec c) = vec (UnOp UnboxKey c) kvec

slReplicateNest :: DVec -> DVec -> Build SL (DVec, RVec)
slReplicateNest (DVec c1) (DVec c2) = pairVec (BinOp ReplicateNest c1 c2) dvec rvec

slReplicateVector :: DVec -> DVec -> Build SL (DVec, RVec)
slReplicateVector (DVec c1) (DVec c2) = pairVec (BinOp ReplicateVector c1 c2) dvec rvec

slReplicateScalar :: DVec -> DVec -> Build SL (DVec, RVec)
slReplicateScalar (DVec c1) (DVec c2) = pairVec (BinOp ReplicateScalar c1 c2) dvec rvec

slUnboxSng :: DVec -> DVec -> Build SL (DVec, KVec)
slUnboxSng (DVec c1) (DVec c2) = pairVec (BinOp UnboxSng c1 c2) dvec kvec

slAppSort :: SVec -> DVec -> Build SL (DVec, SVec)
slAppSort (SVec c1) (DVec c2) = pairVec (BinOp AppSort c1 c2) dvec svec

slAppFilter :: FVec -> DVec -> Build SL (DVec, FVec)
slAppFilter (FVec c1) (DVec c2) = pairVec (BinOp AppFilter c1 c2) dvec fvec

slAppKey :: KVec -> DVec -> Build SL (DVec, KVec)
slAppKey (KVec c1) (DVec c2) = pairVec (BinOp AppKey c1 c2) dvec kvec

slAppRep :: RVec -> DVec -> Build SL (DVec, RVec)
slAppRep (RVec c1) (DVec c2) = pairVec (BinOp AppRep c1 c2) dvec rvec

slNest :: DVec -> Build SL (DVec, DVec)
slNest (DVec c)= pairVec (UnOp Nest c) dvec dvec

slAppend :: DVec -> DVec -> Build SL (DVec, KVec, KVec)
slAppend (DVec c1) (DVec c2) = tripleVec (BinOp Append c1 c2) dvec kvec kvec

slSegment :: DVec -> Build SL DVec
slSegment (DVec c) = vec (UnOp Segment c) dvec

slUnsegment :: DVec -> Build SL DVec
slUnsegment (DVec c) = vec (UnOp Unsegment c) dvec

slCombine :: DVec -> DVec -> DVec -> Build SL (DVec, KVec, KVec)
slCombine (DVec c1) (DVec c2) (DVec c3) =
    tripleVec (TerOp Combine c1 c2 c3) dvec kvec kvec

slLit :: ([Ty.ScalarType], SegFrame, Segments) -> Build SL DVec
slLit i = vec (NullaryOp $ Lit i) dvec

slTableRef :: String -> L.BaseTableSchema -> Build SL DVec
slTableRef n schema = vec (NullaryOp $ TableRef (n, schema)) dvec

slUnExpr :: L.ScalarUnOp -> DVec -> Build SL DVec
slUnExpr o (DVec c) = vec (UnOp (Project [UnApp o (Column 1)]) c) dvec

slBinExpr :: L.ScalarBinOp -> DVec -> DVec -> Build SL DVec
slBinExpr o (DVec c1) (DVec c2) = do
    z <- insert $ BinOp Align c1 c2
    dvec $ insert $ UnOp (Project [BinApp o (Column 1) (Column 2)]) z

slSelect :: Expr -> DVec -> Build SL (DVec, FVec)
slSelect p (DVec c) = pairVec (UnOp (Select p) c) dvec fvec

slProject :: [Expr] -> DVec -> Build SL DVec
slProject projs (DVec c) = dvec $ insert $ UnOp (Project projs) c

slAlign :: DVec -> DVec -> Build SL DVec
slAlign (DVec c1) (DVec c2) = vec (BinOp Align c1 c2) dvec

slZip :: DVec -> DVec -> Build SL (DVec, KVec, KVec)
slZip (DVec c1) (DVec c2) =
    tripleVec (BinOp Zip c1 c2) dvec kvec kvec

slCartProduct :: DVec -> DVec -> Build SL (DVec, RVec, RVec)
slCartProduct (DVec c1) (DVec c2) =
    tripleVec (BinOp CartProduct c1 c2) dvec rvec rvec

slThetaJoin :: L.JoinPredicate L.ScalarExpr -> DVec -> DVec -> Build SL (DVec, RVec, RVec)
slThetaJoin joinPred (DVec c1) (DVec c2) =
    tripleVec (BinOp (ThetaJoin joinPred') c1 c2) dvec rvec rvec
  where
    joinPred' = toSLJoinPred joinPred

slNestJoin :: L.JoinPredicate L.ScalarExpr -> DVec -> DVec -> Build SL (DVec, RVec, RVec)
slNestJoin joinPred (DVec c1) (DVec c2) =
    tripleVec (BinOp (NestJoin joinPred') c1 c2) dvec rvec rvec
  where
    joinPred' = toSLJoinPred joinPred

slGroupJoin :: L.JoinPredicate L.ScalarExpr -> L.NE AggrFun -> DVec -> DVec -> Build SL DVec
slGroupJoin joinPred afuns (DVec c1) (DVec c2) =
    vec (BinOp (GroupJoin (joinPred', afuns)) c1 c2) dvec
  where
    joinPred' = toSLJoinPred joinPred

slSemiJoin :: L.JoinPredicate L.ScalarExpr -> DVec -> DVec -> Build SL (DVec, FVec)
slSemiJoin joinPred (DVec c1) (DVec c2) =
    pairVec (BinOp (SemiJoin joinPred') c1 c2) dvec fvec
  where
    joinPred' = toSLJoinPred joinPred

slAntiJoin :: L.JoinPredicate L.ScalarExpr -> DVec -> DVec -> Build SL (DVec, FVec)
slAntiJoin joinPred (DVec c1) (DVec c2) =
    pairVec (BinOp (AntiJoin joinPred') c1 c2) dvec fvec
  where
    joinPred' = toSLJoinPred joinPred

slReverse :: DVec -> Build SL (DVec, SVec)
slReverse (DVec c) = pairVec (UnOp Reverse c) dvec svec
