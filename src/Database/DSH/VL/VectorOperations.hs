{-# LANGUAGE TemplateHaskell #-}

-- | Vectorising constructor functions that implement FKL primitives
-- using VL operators.
module Database.DSH.VL.VectorOperations where

import           Debug.Trace

import Prelude hiding (reverse, zip)
import qualified Prelude as P
import           Control.Applicative

import           Database.Algebra.Dag.Build

import qualified Database.DSH.Common.Lang       as L
import           Database.DSH.Common.QueryPlan
import           Database.DSH.Common.Type
import qualified Database.DSH.FKL.Lang          as F
import           Database.DSH.Impossible
import           Database.DSH.VL.Lang           (AggrFun (..), Expr (..),
                                                 VL (), VLVal (..))
import           Database.DSH.VL.MetaPrimitives
import           Database.DSH.VL.Vector
import           Database.DSH.VL.VLPrimitives

--------------------------------------------------------------------------------
-- Construction of not-lifted primitives

zip ::  Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
zip (VShape q1 lyt1) (VShape q2 lyt2) = do
    q' <- vlZip q1 q2
    return $ VShape q' $ zipLayout lyt1 lyt2
zip _ _ = $impossible

cartProduct :: Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
cartProduct (VShape q1 lyt1) (VShape q2 lyt2) = do
    (q', p1, p2) <- vlCartProduct q1 q2
    lyt1'        <- chainReorder p1 lyt1
    lyt2'        <- chainReorder p2 lyt2
    return $ VShape q' $ zipLayout lyt1' lyt2'
cartProduct _ _ = $impossible

nestProduct :: Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
nestProduct (VShape q1 lyt1) (VShape q2 lyt2) = do
  q1' <- vlSegment q1
  VShape qj lytJ <- cartProduct (VShape q1' lyt1) (VShape q2 lyt2)
  return $ VShape q1 (LPair lyt1 (LNest qj lytJ))
nestProduct _ _ = $impossible

thetaJoin :: L.JoinPredicate L.JoinExpr -> Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
thetaJoin joinPred (VShape q1 lyt1) (VShape q2 lyt2) = do
    (q', p1, p2) <- vlThetaJoin joinPred q1 q2
    lyt1'        <- chainReorder p1 lyt1
    lyt2'        <- chainReorder p2 lyt2
    return $ VShape q' $ zipLayout lyt1' lyt2'
thetaJoin _ _ _ = $impossible

nestJoin :: L.JoinPredicate L.JoinExpr -> Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
nestJoin joinPred (VShape q1 lyt1) (VShape q2 lyt2) = do
    q1' <- vlSegment q1
    VShape qj lytJ <- thetaJoin joinPred (VShape q1' lyt1) (VShape q2 lyt2)
    return $ VShape q1 (LPair lyt1 (LNest qj lytJ))
nestJoin _ _ _ = $impossible

semiJoin :: L.JoinPredicate L.JoinExpr -> Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
semiJoin joinPred (VShape q1 lyt1) (VShape q2 _) = do
    (qj, r) <- vlSemiJoin joinPred q1 q2
    lyt1'   <- chainRenameFilter r lyt1
    return $ VShape qj lyt1'
semiJoin _ _ _ = $impossible

antiJoin :: L.JoinPredicate L.JoinExpr -> Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
antiJoin joinPred (VShape q1 lyt1) (VShape q2 _) = do
    (qj, r) <- vlAntiJoin joinPred q1 q2
    lyt1'   <- chainRenameFilter r lyt1
    return $ VShape qj lyt1'
antiJoin _ _ _ = $impossible

nub ::  Shape VLDVec -> Build VL (Shape VLDVec)
nub (VShape q lyt) = VShape <$> vlUniqueS q <*> pure lyt
nub _ = $impossible

number ::  Shape VLDVec -> Build VL (Shape VLDVec)
number (VShape q lyt) =
    VShape <$> vlNumber q
                <*> (pure $ zipLayout lyt (LCol 1))
number _ = $impossible

init ::  Shape VLDVec -> Build VL (Shape VLDVec)
init (VShape q lyt) = do
    i          <- vlAggr AggrCount q
    (q', r, _) <- vlSelectPos q (L.SBRelOp L.Lt) i
    lyt'       <- chainRenameFilter r lyt
    return $ VShape q' lyt'
init _ = $impossible

last ::  Shape VLDVec -> Build VL (Shape VLDVec)
last (VShape qs lyt@(LNest _ _)) = do
    i              <- vlAggr AggrCount qs
    (q, r, _)      <- vlSelectPos qs (L.SBRelOp L.Eq) i
    (LNest qr lyt') <- chainRenameFilter r lyt
    re             <- vlUnboxRename q
    renameOuter re $ VShape qr lyt'
last (VShape qs lyt) = do
    i         <- vlAggr AggrCount qs
    (q, r, _) <- vlSelectPos qs (L.SBRelOp L.Eq) i
    lyt'      <- chainRenameFilter r lyt
    return $ SShape q lyt'
last _ = $impossible

index ::  Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
index (VShape qs (LNest qi lyti)) (SShape i _) = do
    one       <- literal intT (VLInt 1)
    i'        <- vlBinExpr (L.SBNumOp L.Add) i one
    -- Use the unboxing rename vector
    (_, _, r) <- vlSelectPos qs (L.SBRelOp L.Eq) i'
    (qu, ri)  <- vlUnbox r qi
    lyti'     <- chainRenameFilter ri lyti
    return $ VShape qu lyti'
index (VShape qs lyt) (SShape i _) = do
    one       <- literal intT (VLInt 1)
    i'        <- vlBinExpr (L.SBNumOp L.Add) i one
    (q, r, _) <- vlSelectPos qs (L.SBRelOp L.Eq) i'
    lyt'      <- chainRenameFilter r lyt
    return $ SShape q lyt'
index _ _ = $impossible

append ::  Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
append = appendVec

-- FIXME looks fishy, there should be an unboxing join.
the ::  Shape VLDVec -> Build VL (Shape VLDVec)
the (VShape d lyt@(LNest _ _)) = do
    (_, prop, _)   <- vlSelectPos1 d (L.SBRelOp L.Eq) 1
    (LNest q' lyt') <- chainRenameFilter prop lyt
    return $ VShape q' lyt'
the (VShape d lyt) = do
    (q', prop, _) <- vlSelectPos1 d (L.SBRelOp L.Eq) 1
    lyt'          <- chainRenameFilter prop lyt
    return $ SShape q' lyt'
the _ = $impossible

reverse ::  Shape VLDVec -> Build VL (Shape VLDVec)
reverse (VShape d lyt) = do
    (d', p) <- vlReverse d
    lyt'    <- chainReorder p lyt
    return (VShape d' lyt')
reverse _ = $impossible

tail ::  Shape VLDVec -> Build VL (Shape VLDVec)
tail (VShape d lyt) = do
    p          <- literal intT (VLInt 1)
    (q', r, _) <- vlSelectPos d (L.SBRelOp L.Gt) p
    lyt'       <- chainRenameFilter r lyt
    return $ VShape q' lyt'
tail _ = $impossible

sort :: Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
sort (VShape q1 _) (VShape q2 lyt2) = do
    (v, p) <- vlSort q1 q2
    lyt2'  <- chainReorder p lyt2
    return $ VShape v lyt2'
sort _e1 _e2 = $impossible

group ::  Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
group (VShape q1 lyt1) (VShape q2 lyt2) = do
    (d, v, p) <- vlGroup q1 q2
    lyt2'     <- chainReorder p lyt2
    return $ VShape d (LPair lyt1 (LNest v lyt2') )
group _e1 _e2 = $impossible

length ::  Shape VLDVec -> Build VL (Shape VLDVec)
length q = do
    v' <- outer q
    v  <- vlAggr AggrCount v'
    return $ SShape v (LCol 1)

cons ::  Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
cons q1@(SShape _ _) q2@(VShape _ _) = do
    n <- singletonAtom q1
    appendVec n q2
cons q1 q2 = do
    n <- singletonVec q1
    appendVec n q2

restrict ::  Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
restrict(VShape q1 lyt) (VShape q2 (LCol 1)) = do
    (v, p) <- vlRestrict (Column 1) q1 q2
    lyt'   <- chainRenameFilter p lyt
    return $ VShape v lyt'
restrict _e1 _e2 = $impossible

combine ::  Shape VLDVec -> Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
combine (VShape qb (LCol 1)) (VShape q1 lyt1) (VShape q2 lyt2) = do
    (v, p1, p2) <- vlCombine qb q1 q2
    lyt1'       <- renameOuter' p1 lyt1
    lyt2'       <- renameOuter' p2 lyt2
    lyt'        <- appendLayout lyt1' lyt2'
    return $ VShape v lyt'
combine _ _ _ = $impossible

dist ::  Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
dist (SShape q lyt) q2 = do
    o      <- outer q2
    (v, p) <- vlDistPrim q o
    lyt'   <- chainReorder p lyt
    return $ VShape v lyt'
dist (VShape q lyt) q2 = do
    o      <- outer q2
    (d, p) <- vlDistDesc q o

    -- The outer vector does not have columns, it only describes the
    -- shape.
    o'     <- vlProject o []
    lyt'   <- chainReorder p lyt
    return $ VShape o' (LNest d lyt')

aggr :: (Expr -> AggrFun) -> Shape VLDVec -> Build VL (Shape VLDVec)
aggr afun (VShape q (LCol 1)) =
    SShape <$> vlAggr (afun (Column 1)) q <*> (pure $ LCol 1)
aggr _ _ = $impossible


ifList ::  Shape VLDVec -> Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
ifList (SShape qb _) (VShape q1 lyt1) (VShape q2 lyt2) = do
    (d1', _)  <- vlDistPrim qb q1
    (d1, p1)  <- vlRestrict (Column 1) q1 d1'
    qb'       <- vlUnExpr (L.SUBoolOp L.Not) qb
    (d2', _)  <- vlDistPrim qb' q2
    (d2, p2)  <- vlRestrict (Column 1) q2 d2'
    lyt1'     <- renameOuter' p1 lyt1
    lyt2'     <- renameOuter' p2 lyt2
    lyt'      <- appendLayout lyt1' lyt2'
    (d, _, _) <- vlAppend d1 d2
    return $ VShape d lyt'
ifList qb (SShape q1 lyt1) (SShape q2 lyt2) = do
    (VShape q lyt) <- ifList qb (VShape q1 lyt1) (VShape q2 lyt2)
    return $ SShape q lyt
ifList _ _ _ = $impossible

pair ::  Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
pair (SShape q1 lyt1) (SShape q2 lyt2) = do
    q <- vlZip q1 q2
    let lyt = zipLayout lyt1 lyt2
    return $ SShape q lyt
pair (VShape q1 lyt1) (VShape q2 lyt2) = do
    d   <- vlLit L.PossiblyEmpty [] [[VLInt 1, VLInt 1]]
    q1' <- vlUnsegment q1
    q2' <- vlUnsegment q2
    let lyt = zipLayout (LNest q1' lyt1) (LNest q2' lyt2)
    return $ SShape d lyt
pair (VShape q1 lyt1) (SShape q2 lyt2) = do
    q1' <- vlUnsegment q1
    let lyt = zipLayout (LNest q1' lyt1) lyt2
    return $ SShape q2 lyt
pair (SShape q1 lyt1) (VShape q2 lyt2) = do
    q2' <- vlUnsegment q2
    let lyt = zipLayout lyt1 (LNest q2' lyt2)
    return $ SShape q1 lyt

fst ::  Shape VLDVec -> Build VL (Shape VLDVec)
fst (SShape _q (LPair (LNest q lyt) _p2)) = return $ VShape q lyt
fst (SShape q (LPair p1 _p2)) = do
    let (p1', cols) = projectFromPos p1
    proj <- vlProject q (map Column cols)
    return $ SShape proj p1'
fst _e1 = $impossible

snd ::  Shape VLDVec -> Build VL (Shape VLDVec)
snd (SShape _q (LPair _p1 (LNest q lyt))) = return $ VShape q lyt
snd (SShape q (LPair _p1 p2)) = do
    let (p2', cols) = projectFromPos p2
    proj <- vlProject q (map Column cols)
    return $ SShape proj p2'
snd _ = $impossible

transpose :: Shape VLDVec -> Build VL (Shape VLDVec)
transpose (VShape _ (LNest qi lyt)) = do
    (qo', qi') <- vlTranspose qi
    return $ VShape qo' (LNest qi' lyt)
transpose _ = $impossible


reshape :: Integer -> Shape VLDVec -> Build VL (Shape VLDVec)
reshape n (VShape q lyt) = do
    (qo, qi) <- vlReshape n q
    return $ VShape qo (LNest qi lyt)
reshape _ _ = $impossible

concat :: Shape VLDVec -> Build VL (Shape VLDVec)
concat (VShape _ (LNest q lyt)) = VShape <$> vlUnsegment q <*> pure lyt
concat _e                           = $impossible


--------------------------------------------------------------------------------
-- Construction of lifted primitives

restrictL :: Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
restrictL (VShape qo (LNest qi lyt)) (VShape _ (LNest qb (LCol 1))) = do
    VShape qi' lyt' <- restrict (VShape qi lyt) (VShape qb (LCol 1))
    return $ VShape qo (LNest qi' lyt')
restrictL _                              _                                      = 
    $impossible

combineL :: Shape VLDVec -> Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
combineL (VShape qo (LNest qb (LCol 1)))
         (VShape _ (LNest qi1 lyt1)) 
         (VShape _ (LNest qi2 lyt2)) = do
    VShape qi' lyt' <- combine (VShape qb (LCol 1)) (VShape qi1 lyt1) (VShape qi2 lyt2)
    return $ VShape qo (LNest qi' lyt')
combineL _ _ _ = $impossible

zipL ::  Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
zipL (VShape d1 (LNest q1 lyt1)) (VShape _ (LNest q2 lyt2)) = do
    (q', r1, r2) <- vlZipS q1 q2
    lyt1'        <- chainRenameFilter r1 lyt1
    lyt2'        <- chainRenameFilter r2 lyt2
    return $ VShape d1 (LNest q' $ zipLayout lyt1' lyt2')
zipL _ _ = $impossible

cartProductL :: Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
cartProductL (VShape d1 (LNest q1 lyt1)) (VShape _ (LNest q2 lyt2)) = do
    (q', p1, p2) <- vlCartProductS q1 q2
    lyt1'        <- chainReorder p1 lyt1
    lyt2'        <- chainReorder p2 lyt2
    return $ VShape d1 (LNest q' $ zipLayout lyt1' lyt2')
cartProductL _ _ = $impossible

nestProductL :: Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
nestProductL (VShape qd1 (LNest qv1 lyt1)) (VShape _qd2 (LNest qv2 lyt2)) = do
    (qj, qp2) <- vlNestProductS qv1 qv2
    lyt2'     <- chainReorder qp2 lyt2
    let lytJ  = zipLayout lyt1 lyt2'
    return $ VShape qd1 (LNest qv1 (LPair lyt1 (LNest qj lytJ)))
nestProductL _ _ = $impossible

thetaJoinL :: L.JoinPredicate L.JoinExpr -> Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
thetaJoinL joinPred (VShape d1 (LNest q1 lyt1)) (VShape _ (LNest q2 lyt2)) = do
    (q', p1, p2) <- vlThetaJoinS joinPred q1 q2
    lyt1'        <- chainReorder p1 lyt1
    lyt2'        <- chainReorder p2 lyt2
    return $ VShape d1 (LNest q' $ zipLayout lyt1' lyt2')
thetaJoinL _ _ _ = $impossible

-- △^L :: [[a]] -> [[b]] -> [[(a, [(a, b)])]]

-- For the unlifted nestjoin, we could segment the left (outer) input
-- and then use the regular thetajoin implementation. This trick does
-- not work here, as the lifted thetajoin joins on the
-- descriptors. Therefore, we have to 'segment' **after** the join,
-- i.e. use the left input positions as descriptors
nestJoinL :: L.JoinPredicate L.JoinExpr -> Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
nestJoinL joinPred (VShape qd1 (LNest qv1 lyt1)) (VShape _qd2 (LNest qv2 lyt2)) = do
    (qj, qp2) <- vlNestJoinS joinPred qv1 qv2
    lyt2'     <- chainReorder qp2 lyt2
    let lytJ  = zipLayout lyt1 lyt2'
    return $ VShape qd1 (LNest qv1 (LPair lyt1 (LNest qj lytJ)))
nestJoinL _ _ _ = $impossible

semiJoinL :: L.JoinPredicate L.JoinExpr -> Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
semiJoinL joinPred (VShape d1 (LNest q1 lyt1)) (VShape _ (LNest q2 _)) = do
    (qj, r) <- vlSemiJoinS joinPred q1 q2
    lyt1'   <- chainRenameFilter r lyt1
    return $ VShape d1 (LNest qj lyt1')
semiJoinL _ _ _ = $impossible

antiJoinL :: L.JoinPredicate L.JoinExpr -> Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
antiJoinL joinPred (VShape d1 (LNest q1 lyt1)) (VShape _ (LNest q2 _)) = do
    (qj, r) <- vlAntiJoinS joinPred q1 q2
    lyt1'   <- chainRenameFilter r lyt1
    return $ VShape d1 (LNest qj lyt1')
antiJoinL _ _ _ = $impossible



nubL ::  Shape VLDVec -> Build VL (Shape VLDVec)
nubL (VShape d (LNest q lyt)) =  VShape d <$> (LNest <$> vlUniqueS q <*> pure lyt)
nubL _ = $impossible

numberL ::  Shape VLDVec -> Build VL (Shape VLDVec)
numberL (VShape d (LNest q lyt)) =
    VShape d <$> (LNest <$> vlNumberS q
                            <*> (pure $ zipLayout lyt (LCol 1)))
numberL _ = $impossible

initL ::  Shape VLDVec -> Build VL (Shape VLDVec)
initL (VShape qs (LNest q lyt)) = do
    is         <- vlAggrS AggrCount qs q
    (q', r, _) <- vlSelectPosS q (L.SBRelOp L.Lt) is
    lyt'       <- chainRenameFilter r lyt
    return $ VShape qs (LNest q' lyt')
initL _ = $impossible

lastL ::  Shape VLDVec -> Build VL (Shape VLDVec)
lastL (VShape d (LNest qs lyt@(LNest _ _))) = do
    is          <- vlAggrS AggrCount d qs
    (qs', r, _) <- vlSelectPosS qs (L.SBRelOp L.Eq) is
    lyt'        <- chainRenameFilter r lyt
    re          <- vlUnboxRename qs'
    VShape d <$> renameOuter' re lyt'
lastL (VShape d (LNest qs lyt)) = do
    is          <- vlAggrS AggrCount d qs
    (qs', r, _) <- vlSelectPosS qs (L.SBRelOp L.Eq) is
    lyt'        <- chainRenameFilter r lyt
    re          <- vlUnboxRename d
    renameOuter re (VShape qs' lyt')
lastL _ = $impossible

indexL ::  Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
indexL (VShape d (LNest qs (LNest qi lyti))) (VShape is (LCol 1)) = do
    one       <- literal intT (VLInt 1)
    (ones, _) <- vlDistPrim one is
    is'       <- vlBinExpr (L.SBNumOp L.Add) is ones
    (_, _, u) <- vlSelectPosS qs (L.SBRelOp L.Eq) is'
    (qu, ri)  <- vlUnbox u qi
    lyti'     <- chainRenameFilter ri lyti
    return $ VShape d (LNest qu lyti')
indexL (VShape d (LNest qs lyt)) (VShape is (LCol 1)) = do
    one         <- literal intT (VLInt 1)
    (ones, _)   <- vlDistPrim one is
    is'         <- vlBinExpr (L.SBNumOp L.Add) is ones
    (qs', r, _) <- vlSelectPosS qs (L.SBRelOp L.Eq) is'
    lyt'        <- chainRenameFilter r lyt
    re          <- vlUnboxRename d
    renameOuter re (VShape qs' lyt')
indexL _ _ = $impossible

appendL ::  Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
appendL (VShape d lyt1) (VShape _ lyt2) = do
    VShape d <$> appendLayout lyt1 lyt2
appendL _ _ = $impossible

reverseL ::  Shape VLDVec -> Build VL (Shape VLDVec)
reverseL (VShape d (LNest d1 lyt)) = do
    (d1', p) <- vlReverseS d1
    lyt'     <- chainReorder p lyt
    return (VShape d (LNest d1' lyt'))
reverseL _ = $impossible

theL ::  Shape VLDVec -> Build VL (Shape VLDVec)
theL (VShape d (LNest q lyt)) = do
    (v, p2, _) <- vlSelectPos1S q (L.SBRelOp L.Eq) 1
    prop       <- vlUnboxRename d
    lyt'       <- chainRenameFilter p2 lyt
    v'         <- vlPropRename prop v
    return $ VShape v' lyt'
theL _ = $impossible

tailL ::  Shape VLDVec -> Build VL (Shape VLDVec)
tailL (VShape d (LNest q lyt)) = do
    one        <- literal intT (VLInt 1)
    (p, _)     <- vlDistPrim one d
    (v, p2, _) <- vlSelectPosS q (L.SBRelOp L.Gt) p
    lyt'       <- chainRenameFilter p2 lyt
    return $ VShape d (LNest v lyt')
tailL _ = $impossible

sortL ::  Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
sortL (VShape _ (LNest v1 _)) (VShape d2 (LNest v2 lyt2)) = do
    (v, p) <- vlSort v1 v2
    lyt2'  <- chainReorder p lyt2
    return $ VShape d2 (LNest v lyt2')
sortL _ _ = $impossible

groupL ::  Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
groupL (VShape _ (LNest v1 lyt1)) (VShape d2 (LNest v2 lyt2)) = do
    (d, v, p) <- vlGroup v1 v2
    lyt2'     <- chainReorder p lyt2
    return $ VShape d2 (LNest d (LPair lyt1 (LNest v lyt2')))
groupL _ _ = $impossible

concatL ::  Shape VLDVec -> Build VL (Shape VLDVec)
concatL (VShape d (LNest d' vs)) = do
    p   <- vlUnboxRename d'
    vs' <- renameOuter' p vs
    return $ VShape d vs'
concatL _ = $impossible

lengthL ::  Shape VLDVec -> Build VL (Shape VLDVec)
lengthL (VShape q (LNest qi _)) = do
    ls <- vlAggrS AggrCount q qi
    return $ VShape ls (LCol 1)
lengthL s = trace (show s) $ $impossible

consL ::  Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
consL (VShape q1 lyt1) (VShape q2 (LNest qi lyt2)) = do
    s           <- vlSegment q1
    (v, p1, p2) <- vlAppendS s qi
    lyt1'       <- renameOuter' p1 lyt1
    lyt2'       <- renameOuter' p2 lyt2
    lyt'        <- appendLayout lyt1' lyt2'
    return $ VShape q2 (LNest v lyt')
consL _ _ = $impossible


outer ::  Shape VLDVec -> Build VL VLDVec
outer (SShape _ _)            = $impossible
outer (VShape q _)        = return q

aggrL :: (Expr -> AggrFun) -> Shape VLDVec -> Build VL (Shape VLDVec)
aggrL afun (VShape d (LNest q (LCol 1))) = do
    qr <- vlAggrS (afun (Column 1)) d q
    return $ VShape qr (LCol 1)
aggrL _ _ = $impossible

distL ::  Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
distL (VShape q1 lyt1) (VShape d (LNest q2 lyt2)) = do
    (qa, p)             <- vlAlign q1 q2
    lyt1'               <- chainReorder p lyt1
    let lyt             = zipLayout lyt1' lyt2
    VShape qf lytf <- fstL $ VShape qa lyt
    return $ VShape d (LNest qf lytf)
distL _e1 _e2 = $impossible


pairL ::  Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
pairL (VShape q1 lyt1) (VShape q2 lyt2) = do
    q <- vlZip q1 q2
    let lyt = zipLayout lyt1 lyt2
    return $ VShape q lyt
pairL _ _ = $impossible

fstL ::  Shape VLDVec -> Build VL (Shape VLDVec)
fstL (VShape q (LPair p1 _p2)) = do
    let(p1', cols) = projectFromPos p1
    proj <- vlProject q (map Column cols)
    return $ VShape proj p1'
fstL _s = $impossible

sndL ::  Shape VLDVec -> Build VL (Shape VLDVec)
sndL (VShape q (LPair _p1 p2)) = do
    let (p2', cols) = projectFromPos p2
    proj <- vlProject q (map Column cols)
    return $ VShape proj p2'
sndL s = trace (show s) $ $impossible

transposeL :: Shape VLDVec -> Build VL (Shape VLDVec)
transposeL (VShape qo (LNest qm (LNest qi lyt))) = do
    (qm', qi') <- vlTransposeS qm qi
    return $ VShape qo (LNest qm' (LNest qi' lyt))
transposeL _ = $impossible

reshapeL :: Integer -> Shape VLDVec -> Build VL (Shape VLDVec)
reshapeL n (VShape qo (LNest qi lyt)) = do
    (qm, qi') <- vlReshapeS n qi
    return $ VShape qo (LNest qm (LNest qi' lyt))
reshapeL _ _ = $impossible

projectFromPos :: Layout VLDVec -> (Layout VLDVec , [DBCol])
projectFromPos = (\(x,y,_) -> (x,y)) . (projectFromPosWork 1)
  where
    projectFromPosWork :: Int -> Layout VLDVec -> (Layout VLDVec, [DBCol], Int)
    projectFromPosWork c (LCol i)      = (LCol c, [i], c + 1)
    projectFromPosWork c (LNest q l)   = (LNest q l, [], c)
    projectFromPosWork c (LPair p1 p2) = let (p1', cols1, c')  = projectFromPosWork c p1
                                             (p2', cols2, c'') = projectFromPosWork c' p2
                                         in (LPair p1' p2', cols1 ++ cols2, c'')

singletonVec ::  Shape VLDVec -> Build VL (Shape VLDVec)
singletonVec (VShape q lyt) = do
    VLDVec d <- vlSingletonDescr
    return $ VShape (VLDVec d) (LNest q lyt)
singletonVec _ = $impossible

singletonAtom ::  Shape VLDVec -> Build VL (Shape VLDVec)
singletonAtom (SShape q1 lyt) = return $ VShape q1 lyt
singletonAtom _ = $impossible

--------------------------------------------------------------------------------
-- Construction of base tables and literal tables

dbTable ::  String -> [L.Column] -> L.TableHints -> Build VL (Shape VLDVec)
dbTable n cs ks = do
    t <- vlTableRef n (map (mapSnd typeToRowType) cs) ks
    return $ VShape t (foldr1 LPair [LCol i | i <- [1..P.length cs]])

mkLiteral ::  Type -> L.Val -> Build VL (Shape VLDVec)
mkLiteral t@(ListT _) (L.ListV es) = do
    ((descHd, descV), lyt, _) <- toPlan (mkDescriptor [P.length es]) t 1 es
    let emptinessFlag = case es of
          []    -> L.PossiblyEmpty
          _ : _ -> L.NonEmpty
    litNode <- vlLit emptinessFlag (P.reverse descHd) $ map P.reverse descV
    return $ VShape litNode lyt
mkLiteral (FunT _ _) _  = $impossible
mkLiteral t e           = do
    ((descHd, [descV]), layout, _) <- toPlan (mkDescriptor [1]) (ListT t) 1 [e]
    litNode <- vlLit L.NonEmpty (P.reverse descHd) [(P.reverse descV)]
    return $ SShape litNode layout

type Table = ([Type], [[VLVal]])

-- FIXME Check if inner list literals are nonempty and flag VL
-- literals appropriately.
toPlan ::  Table -> Type -> Int -> [L.Val] -> Build VL (Table, Layout VLDVec, Int)
toPlan (descHd, descV) (ListT t) c es =
    case t of
        PairT t1 t2 -> do
            let (e1s, e2s) = unzip $ map splitVal es
            (desc', l1, c')   <- toPlan (descHd, descV) (ListT t1) c e1s
            (desc'', l2, c'') <- toPlan desc' (ListT t2) c' e2s
            return (desc'', LPair l1 l2, c'')

        ListT _ -> do
            let vs = map fromListVal es
                d  = mkDescriptor $ map P.length vs
            ((hd, vs'), l, _) <- toPlan d t 1 (P.concat vs)
            n <- vlLit L.PossiblyEmpty (P.reverse hd) (map P.reverse vs')
            return ((descHd, descV), LNest n l, c)

        FunT _ _ -> $impossible

        _ -> let (hd, vs) = mkColumn t es
             in return ((hd:descHd, zipWith (:) vs descV), (LCol c), c + 1)

toPlan _ (FunT _ _) _ _ = $impossible
toPlan (descHd, descV) t c v =
    let (hd, v') = mkColumn t v
    in return $ ((hd:descHd, zipWith (:) v' descV), (LCol c), c + 1)

literal :: Type -> VLVal -> Build VL VLDVec
literal t v = vlLit L.NonEmpty [t] [[VLInt 1, VLInt 1, v]]

fromListVal :: L.Val -> [L.Val]
fromListVal (L.ListV es) = es
fromListVal _            = $impossible

splitVal :: L.Val -> (L.Val, L.Val)
splitVal (L.PairV e1 e2) = (e1, e2)
splitVal _                = $impossible

mkColumn :: Type -> [L.Val] -> (Type, [VLVal])
mkColumn t vs = (t, [pVal v | v <- vs])

mkDescriptor :: [Int] -> Table
mkDescriptor lengths =
    let header = []
        body   = map (\(d, p) -> [VLInt $ fromInteger p, VLInt $ fromInteger d])
                 $ P.zip (P.concat [ replicate l p | (p, l) <- P.zip [1..] lengths] ) [1..]
    in (header, body)

--------------------------------------------------------------------------------
-- Helper functions for layouts

zipLayout :: Layout VLDVec -> Layout VLDVec -> Layout VLDVec
zipLayout l1 l2 = let offSet = columnsInLayout l1
                      l2' = incrementPositions offSet l2
                   in LPair l1 l2'

incrementPositions :: Int -> Layout VLDVec -> Layout VLDVec
incrementPositions i (LCol n)       = LCol $ n + i
incrementPositions _i v@(LNest _ _) = v
incrementPositions i (LPair l1 l2)  = LPair (incrementPositions i l1) (incrementPositions i l2)

--------------------------------------------------------------------------------
-- Compile-time operations that implement higher-lifted primitives.

-- | Remove the 'n' outer layers of nesting from a nested list
-- (Prins/Palmer: 'extract').
qConcat :: L.Nat -> Shape VLDVec -> Shape VLDVec
qConcat L.Zero _ = $impossible
qConcat (L.Succ L.Zero) (VShape _ (LNest q lyt)) = VShape q lyt
qConcat (L.Succ n)      (VShape _ lyt)           = extractInnerVec n lyt
qConcat _               _                        = $impossible

extractInnerVec :: L.Nat -> Layout VLDVec -> Shape VLDVec
extractInnerVec (L.Succ L.Zero) (LNest _ (LNest q lyt)) = VShape q lyt
extractInnerVec (L.Succ n)      (LNest _ lyt)           = extractInnerVec n lyt
extractInnerVec _               _                       = $impossible

-- | Prepend the 'n' outer layers of nesting from the first input to
-- the second input (Prins/Palmer: 'insert').
unconcat :: L.Nat -> Shape VLDVec -> Shape VLDVec -> Shape VLDVec
unconcat (L.Succ L.Zero) (VShape d _) (VShape vi lyti) =
    VShape d (LNest vi lyti)
unconcat (L.Succ n) (VShape d lyt) (VShape vi lyti)    = 
    VShape d (implantInnerVec n lyt vi lyti)
unconcat _          _                   _              = 
    $impossible

implantInnerVec :: L.Nat -> Layout VLDVec -> VLDVec -> Layout VLDVec -> Layout VLDVec
implantInnerVec (L.Succ L.Zero) (LNest d _)   vi lyti = 
    LNest d $ LNest vi lyti
implantInnerVec (L.Succ n)      (LNest d lyt) vi lyti = 
    LNest d $ implantInnerVec n lyt vi lyti
implantInnerVec _          _            _  _          = 
    $impossible
