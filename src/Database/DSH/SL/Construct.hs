{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- | Constructor functions for Segment Language primitives
module Database.DSH.SL.Construct where

import qualified Database.DSH.Common.Lang       as L
import           Database.DSH.Common.Vector
import           Database.DSH.Common.VectorLang
import           Database.DSH.Common.Nat

import           Database.Algebra.Dag.Build
import           Database.Algebra.Dag.Common
import           Database.DSH.SL.Lang

--------------------------------------------------------------------------------
-- Construct different types of vectors from algebraic nodes

type VecConst r v = Build RSL AlgNode -> Build RSL v

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
-- Insert RSL operators and appropriate R1/R2/R3 nodes

vec :: RSL -> VecConst r a -> Build RSL a
vec op mkVec = mkVec $ insert op

pairVec :: RSL -> VecConst r a -> VecConst r b -> Build RSL (a, b)
pairVec op mkVec1 mkVec2 = do
    r <- insert op
    r1 <- mkVec1 $ insert $ UnOp R1 r
    r2 <- mkVec2 $ insert $ UnOp R2 r
    return (r1, r2)

tripleVec :: RSL
          -> VecConst r a
          -> VecConst r b
          -> VecConst r c
          -> Build RSL (a, b ,c)
tripleVec op mkVec1 mkVec2 mkVec3 = do
    r <- insert op
    r1 <- mkVec1 $ insert $ UnOp R1 r
    r2 <- mkVec2 $ insert $ UnOp R2 r
    r3 <- mkVec3 $ insert $ UnOp R3 r
    return (r1, r2, r3)

--------------------------------------------------------------------------------

mapSnd :: (b -> c) -> (a, b) -> (a, c)
mapSnd f (a, b) = (a, f b)

----------------------------------------------------------------------------------
-- DAG constructor functions for RSL operators

slUnique :: DVec -> Build RSL DVec
slUnique (DVec c) = vec (UnOp Unique c) dvec

slNumber :: DVec -> Build RSL DVec
slNumber (DVec c) = vec (UnOp Number c) dvec

slGroup :: VectorExpr -> DVec -> Build RSL (DVec, DVec, SVec)
slGroup groupExprs (DVec c) = tripleVec (UnOp (Group groupExprs) c) dvec dvec svec

slSort :: VectorExpr -> DVec -> Build RSL (DVec, SVec)
slSort sortExprs (DVec c1) = pairVec (UnOp (Sort sortExprs) c1) dvec svec

slFold :: AggrFun VectorExpr -> DVec -> DVec -> Build RSL DVec
slFold aFun (DVec c1) (DVec c2) = vec (BinOp (Fold aFun) c1 c2) dvec

slUnboxKey :: DVec -> Build RSL KVec
slUnboxKey (DVec c) = vec (UnOp UnboxKey c) kvec

slReplicateNest :: DVec -> DVec -> Build RSL (DVec, RVec)
slReplicateNest (DVec c1) (DVec c2) = pairVec (BinOp ReplicateNest c1 c2) dvec rvec

slReplicateVector :: DVec -> DVec -> Build RSL (DVec, RVec)
slReplicateVector (DVec c1) (DVec c2) = pairVec (BinOp ReplicateVector c1 c2) dvec rvec

slReplicateScalar :: DVec -> DVec -> Build RSL (DVec, RVec)
slReplicateScalar (DVec c1) (DVec c2) = pairVec (BinOp ReplicateScalar c1 c2) dvec rvec

slUnboxSng :: DVec -> DVec -> Build RSL (DVec, KVec)
slUnboxSng (DVec c1) (DVec c2) = pairVec (BinOp UnboxSng c1 c2) dvec kvec

slAppSort :: SVec -> DVec -> Build RSL (DVec, SVec)
slAppSort (SVec c1) (DVec c2) = pairVec (BinOp AppSort c1 c2) dvec svec

slAppFilter :: FVec -> DVec -> Build RSL (DVec, FVec)
slAppFilter (FVec c1) (DVec c2) = pairVec (BinOp AppFilter c1 c2) dvec fvec

slAppKey :: KVec -> DVec -> Build RSL (DVec, KVec)
slAppKey (KVec c1) (DVec c2) = pairVec (BinOp AppKey c1 c2) dvec kvec

slAppRep :: RVec -> DVec -> Build RSL (DVec, RVec)
slAppRep (RVec c1) (DVec c2) = pairVec (BinOp AppRep c1 c2) dvec rvec

slAppend :: DVec -> DVec -> Build RSL (DVec, KVec, KVec)
slAppend (DVec c1) (DVec c2) = tripleVec (BinOp Append c1 c2) dvec kvec kvec

slSegment :: DVec -> Build RSL DVec
slSegment (DVec c) = vec (UnOp Segment c) dvec

slUnsegment :: DVec -> Build RSL DVec
slUnsegment (DVec c) = vec (UnOp Unsegment c) dvec

slCombine :: DVec -> DVec -> DVec -> Build RSL (DVec, KVec, KVec)
slCombine (DVec c1) (DVec c2) (DVec c3) =
    tripleVec (TerOp Combine c1 c2 c3) dvec kvec kvec

slLit :: (PType, VecSegs) -> Build RSL DVec
slLit i = vec (NullaryOp $ Lit i) dvec

slTableRef :: String -> L.BaseTableSchema -> Build RSL DVec
slTableRef n schema = vec (NullaryOp $ TableRef (n, schema)) dvec

slUnExpr :: L.ScalarUnOp -> DVec -> Build RSL DVec
slUnExpr o (DVec c) = vec (UnOp (Project (VUnApp o VInput)) c) dvec

slBinExpr :: L.ScalarBinOp -> DVec -> DVec -> Build RSL DVec
slBinExpr o (DVec c1) (DVec c2) = do
    z <- insert $ BinOp Align c1 c2
    dvec $ insert $ UnOp (Project (VBinApp o (VTupElem First VInput) (VTupElem (Next First) VInput))) z

slSelect :: VectorExpr -> DVec -> Build RSL (DVec, FVec)
slSelect p (DVec c) = pairVec (UnOp (Select p) c) dvec fvec

slProject :: VectorExpr -> DVec -> Build RSL DVec
slProject e (DVec c) = dvec $ insert $ UnOp (Project e) c

slAlign :: DVec -> DVec -> Build RSL DVec
slAlign (DVec c1) (DVec c2) = vec (BinOp Align c1 c2) dvec

slZip :: DVec -> DVec -> Build RSL (DVec, RVec, RVec)
slZip (DVec c1) (DVec c2) =
    tripleVec (BinOp Zip c1 c2) dvec rvec rvec

slCartProduct :: DVec -> DVec -> Build RSL (DVec, RVec, RVec)
slCartProduct (DVec c1) (DVec c2) =
    tripleVec (BinOp CartProduct c1 c2) dvec rvec rvec

slThetaJoin :: L.JoinPredicate L.ScalarExpr -> DVec -> DVec -> Build RSL (DVec, RVec, RVec)
slThetaJoin joinPred (DVec c1) (DVec c2) =
    tripleVec (BinOp (ThetaJoin joinPred') c1 c2) dvec rvec rvec
  where
    joinPred' = fmap scalarExpr joinPred

slNestJoin :: L.JoinPredicate L.ScalarExpr -> DVec -> DVec -> Build RSL (DVec, RVec, RVec)
slNestJoin joinPred (DVec c1) (DVec c2) =
    tripleVec (BinOp (NestJoin joinPred') c1 c2) dvec rvec rvec
  where
    joinPred' = fmap scalarExpr joinPred

slGroupJoin :: L.JoinPredicate L.ScalarExpr -> L.NE (AggrFun VectorExpr) -> DVec -> DVec -> Build RSL DVec
slGroupJoin joinPred afuns (DVec c1) (DVec c2) =
    vec (BinOp (GroupJoin (joinPred', afuns)) c1 c2) dvec
  where
    joinPred' = fmap scalarExpr joinPred

slSemiJoin :: L.JoinPredicate L.ScalarExpr -> DVec -> DVec -> Build RSL (DVec, FVec)
slSemiJoin joinPred (DVec c1) (DVec c2) =
    pairVec (BinOp (SemiJoin joinPred') c1 c2) dvec fvec
  where
    joinPred' = fmap scalarExpr joinPred

slAntiJoin :: L.JoinPredicate L.ScalarExpr -> DVec -> DVec -> Build RSL (DVec, FVec)
slAntiJoin joinPred (DVec c1) (DVec c2) =
    pairVec (BinOp (AntiJoin joinPred') c1 c2) dvec fvec
  where
    joinPred' = fmap scalarExpr joinPred

slReverse :: DVec -> Build RSL (DVec, SVec)
slReverse (DVec c) = pairVec (UnOp Reverse c) dvec svec
