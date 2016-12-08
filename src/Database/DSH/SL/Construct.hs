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

type VecConst r v = Build TSL AlgNode -> Build TSL v

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
-- Insert TSL operators and appropriate R1/R2/R3 nodes

vec :: TSL -> VecConst r a -> Build TSL a
vec op mkVec = mkVec $ insert op

pairVec :: TSL -> VecConst r a -> VecConst r b -> Build TSL (a, b)
pairVec op mkVec1 mkVec2 = do
    r <- insert op
    r1 <- mkVec1 $ insert $ SL $ UnOp R1 r
    r2 <- mkVec2 $ insert $ SL $ UnOp R2 r
    return (r1, r2)

tripleVec :: TSL
          -> VecConst r a
          -> VecConst r b
          -> VecConst r c
          -> Build TSL (a, b ,c)
tripleVec op mkVec1 mkVec2 mkVec3 = do
    r <- insert op
    r1 <- mkVec1 $ insert $ SL $ UnOp R1 r
    r2 <- mkVec2 $ insert $ SL $ UnOp R2 r
    r3 <- mkVec3 $ insert $ SL $ UnOp R3 r
    return (r1, r2, r3)

--------------------------------------------------------------------------------

mapSnd :: (b -> c) -> (a, b) -> (a, c)
mapSnd f (a, b) = (a, f b)

----------------------------------------------------------------------------------
-- DAG constructor functions for TSL operators

slUnique :: DVec -> Build TSL DVec
slUnique (DVec c) = vec (SL $ UnOp Unique c) dvec

slNumber :: DVec -> Build TSL DVec
slNumber (DVec c) = vec (SL $ UnOp Number c) dvec

slGroup :: TExpr -> DVec -> Build TSL (DVec, DVec, SVec)
slGroup groupExprs (DVec c) = tripleVec (SL $ UnOp (Group groupExprs) c) dvec dvec svec

slSort :: TExpr -> DVec -> Build TSL (DVec, SVec)
slSort sortExprs (DVec c1) = pairVec (SL $ UnOp (Sort sortExprs) c1) dvec svec

slFold :: AggrFun TExpr -> DVec -> Build TSL DVec
slFold aFun (DVec c) = vec (SL $ UnOp (Fold aFun) c) dvec

slUnboxKey :: DVec -> Build TSL KVec
slUnboxKey (DVec c) = vec (SL $ UnOp UnboxKey c) kvec

slReplicateNest :: DVec -> DVec -> Build TSL (DVec, RVec)
slReplicateNest (DVec c1) (DVec c2) = pairVec (SL $ BinOp ReplicateNest c1 c2) dvec rvec

slReplicateVector :: DVec -> DVec -> Build TSL (DVec, RVec)
slReplicateVector (DVec c1) (DVec c2) = pairVec (SL $ BinOp ReplicateVector c1 c2) dvec rvec

slReplicateScalar :: DVec -> DVec -> Build TSL (DVec, RVec)
slReplicateScalar (DVec c1) (DVec c2) = pairVec (SL $ BinOp ReplicateScalar c1 c2) dvec rvec

slUnboxSng :: DVec -> DVec -> Build TSL (DVec, KVec)
slUnboxSng (DVec c1) (DVec c2) = pairVec (SL $ BinOp UnboxSng c1 c2) dvec kvec

slUnboxDefault :: TExpr -> DVec -> DVec -> Build TSL DVec
slUnboxDefault e (DVec c1) (DVec c2) = vec (SL $ BinOp (UnboxDefault e) c1 c2) dvec

slAppSort :: SVec -> DVec -> Build TSL (DVec, SVec)
slAppSort (SVec c1) (DVec c2) = pairVec (SL $ BinOp AppSort c1 c2) dvec svec

slAppFilter :: FVec -> DVec -> Build TSL (DVec, FVec)
slAppFilter (FVec c1) (DVec c2) = pairVec (SL $ BinOp AppFilter c1 c2) dvec fvec

slAppKey :: KVec -> DVec -> Build TSL (DVec, KVec)
slAppKey (KVec c1) (DVec c2) = pairVec (SL $ BinOp AppKey c1 c2) dvec kvec

slAppRep :: RVec -> DVec -> Build TSL (DVec, RVec)
slAppRep (RVec c1) (DVec c2) = pairVec (SL $ BinOp AppRep c1 c2) dvec rvec

slAppend :: DVec -> DVec -> Build TSL (DVec, KVec, KVec)
slAppend (DVec c1) (DVec c2) = tripleVec (SL $ BinOp Append c1 c2) dvec kvec kvec

slSegment :: DVec -> Build TSL DVec
slSegment (DVec c) = vec (SL $ UnOp Segment c) dvec

slUnsegment :: DVec -> Build TSL DVec
slUnsegment (DVec c) = vec (SL $ UnOp Unsegment c) dvec

slCombine :: DVec -> DVec -> DVec -> Build TSL (DVec, KVec, KVec)
slCombine (DVec c1) (DVec c2) (DVec c3) =
    tripleVec (SL $ TerOp Combine c1 c2 c3) dvec kvec kvec

slLit :: (PType, VecSegs) -> Build TSL DVec
slLit i = vec (SL $ NullaryOp $ Lit i) dvec

slTableRef :: String -> L.BaseTableSchema -> Build TSL DVec
slTableRef n schema = vec (SL $ NullaryOp $ TableRef (n, schema)) dvec

slUnExpr :: L.ScalarUnOp -> DVec -> Build TSL DVec
slUnExpr o (DVec c) = vec (SL $ UnOp (Project (TUnApp o TInput)) c) dvec

slBinExpr :: L.ScalarBinOp -> DVec -> DVec -> Build TSL DVec
slBinExpr o (DVec c1) (DVec c2) = do
    z <- insert $ SL $ BinOp Align c1 c2
    dvec $ insert $ SL $ UnOp (Project (TBinApp o (TTupElem First TInput) (TTupElem (Next First) TInput))) z

slSelect :: TExpr -> DVec -> Build TSL (DVec, FVec)
slSelect p (DVec c) = pairVec (SL $ UnOp (Select p) c) dvec fvec

slProject :: TExpr -> DVec -> Build TSL DVec
slProject e (DVec c) = dvec $ insert $ SL $ UnOp (Project e) c

slAlign :: DVec -> DVec -> Build TSL DVec
slAlign (DVec c1) (DVec c2) = vec (SL $ BinOp Align c1 c2) dvec

slZip :: DVec -> DVec -> Build TSL (DVec, RVec, RVec)
slZip (DVec c1) (DVec c2) =
    tripleVec (SL $ BinOp Zip c1 c2) dvec rvec rvec

slCartProduct :: DVec -> DVec -> Build TSL (DVec, RVec, RVec)
slCartProduct (DVec c1) (DVec c2) =
    tripleVec (SL $ BinOp CartProduct c1 c2) dvec rvec rvec

slThetaJoin :: L.JoinPredicate L.ScalarExpr -> DVec -> DVec -> Build TSL (DVec, RVec, RVec)
slThetaJoin joinPred (DVec c1) (DVec c2) =
    tripleVec (SL $ BinOp (ThetaJoin joinPred') c1 c2) dvec rvec rvec
  where
    joinPred' = fmap scalarExpr joinPred

slNestJoin :: L.JoinPredicate L.ScalarExpr -> DVec -> DVec -> Build TSL (DVec, RVec, RVec)
slNestJoin joinPred (DVec c1) (DVec c2) =
    tripleVec (SL $ BinOp (NestJoin joinPred') c1 c2) dvec rvec rvec
  where
    joinPred' = fmap scalarExpr joinPred

slGroupJoin :: L.JoinPredicate L.ScalarExpr -> L.NE (AggrFun TExpr) -> DVec -> DVec -> Build TSL DVec
slGroupJoin joinPred afuns (DVec c1) (DVec c2) =
    vec (SL $ BinOp (GroupJoin (joinPred', afuns)) c1 c2) dvec
  where
    joinPred' = fmap scalarExpr joinPred

slSemiJoin :: L.JoinPredicate L.ScalarExpr -> DVec -> DVec -> Build TSL (DVec, FVec)
slSemiJoin joinPred (DVec c1) (DVec c2) =
    pairVec (SL $ BinOp (SemiJoin joinPred') c1 c2) dvec fvec
  where
    joinPred' = fmap scalarExpr joinPred

slAntiJoin :: L.JoinPredicate L.ScalarExpr -> DVec -> DVec -> Build TSL (DVec, FVec)
slAntiJoin joinPred (DVec c1) (DVec c2) =
    pairVec (SL $ BinOp (AntiJoin joinPred') c1 c2) dvec fvec
  where
    joinPred' = fmap scalarExpr joinPred

slReverse :: DVec -> Build TSL (DVec, SVec)
slReverse (DVec c) = pairVec (SL $ UnOp Reverse c) dvec svec
