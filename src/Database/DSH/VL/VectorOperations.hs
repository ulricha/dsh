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
zip (ValueVector q1 lyt1) (ValueVector q2 lyt2) = do
    q' <- vlZip q1 q2
    return $ ValueVector q' $ zipLayout lyt1 lyt2
zip _ _ = $impossible

cartProduct :: Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
cartProduct (ValueVector q1 lyt1) (ValueVector q2 lyt2) = do
    (q', p1, p2) <- vlCartProduct q1 q2
    lyt1'        <- chainReorder p1 lyt1
    lyt2'        <- chainReorder p2 lyt2
    return $ ValueVector q' $ zipLayout lyt1' lyt2'
cartProduct _ _ = $impossible

nestProduct :: Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
nestProduct (ValueVector q1 lyt1) (ValueVector q2 lyt2) = do
  q1' <- vlSegment q1
  ValueVector qj lytJ <- cartProduct (ValueVector q1' lyt1) (ValueVector q2 lyt2)
  return $ ValueVector q1 (Pair lyt1 (Nest qj lytJ))
nestProduct _ _ = $impossible

thetaJoin :: L.JoinPredicate L.JoinExpr -> Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
thetaJoin joinPred (ValueVector q1 lyt1) (ValueVector q2 lyt2) = do
    (q', p1, p2) <- vlThetaJoin joinPred q1 q2
    lyt1'        <- chainReorder p1 lyt1
    lyt2'        <- chainReorder p2 lyt2
    return $ ValueVector q' $ zipLayout lyt1' lyt2'
thetaJoin _ _ _ = $impossible

nestJoin :: L.JoinPredicate L.JoinExpr -> Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
nestJoin joinPred (ValueVector q1 lyt1) (ValueVector q2 lyt2) = do
    q1' <- vlSegment q1
    ValueVector qj lytJ <- thetaJoin joinPred (ValueVector q1' lyt1) (ValueVector q2 lyt2)
    return $ ValueVector q1 (Pair lyt1 (Nest qj lytJ))
nestJoin _ _ _ = $impossible

semiJoin :: L.JoinPredicate L.JoinExpr -> Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
semiJoin joinPred (ValueVector q1 lyt1) (ValueVector q2 _) = do
    (qj, r) <- vlSemiJoin joinPred q1 q2
    lyt1'   <- chainRenameFilter r lyt1
    return $ ValueVector qj lyt1'
semiJoin _ _ _ = $impossible

antiJoin :: L.JoinPredicate L.JoinExpr -> Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
antiJoin joinPred (ValueVector q1 lyt1) (ValueVector q2 _) = do
    (qj, r) <- vlAntiJoin joinPred q1 q2
    lyt1'   <- chainRenameFilter r lyt1
    return $ ValueVector qj lyt1'
antiJoin _ _ _ = $impossible

nub ::  Shape VLDVec -> Build VL (Shape VLDVec)
nub (ValueVector q lyt) = ValueVector <$> vlUniqueS q <*> pure lyt
nub _ = $impossible

number ::  Shape VLDVec -> Build VL (Shape VLDVec)
number (ValueVector q lyt) =
    ValueVector <$> vlNumber q
                <*> (pure $ zipLayout lyt (InColumn 1))
number _ = $impossible

init ::  Shape VLDVec -> Build VL (Shape VLDVec)
init (ValueVector q lyt) = do
    i          <- vlAggr AggrCount q
    (q', r, _) <- vlSelectPos q (L.SBRelOp L.Lt) i
    lyt'       <- chainRenameFilter r lyt
    return $ ValueVector q' lyt'
init _ = $impossible

last ::  Shape VLDVec -> Build VL (Shape VLDVec)
last (ValueVector qs lyt@(Nest _ _)) = do
    i              <- vlAggr AggrCount qs
    (q, r, _)      <- vlSelectPos qs (L.SBRelOp L.Eq) i
    (Nest qr lyt') <- chainRenameFilter r lyt
    re             <- vlUnboxRename q
    renameOuter re $ ValueVector qr lyt'
last (ValueVector qs lyt) = do
    i         <- vlAggr AggrCount qs
    (q, r, _) <- vlSelectPos qs (L.SBRelOp L.Eq) i
    lyt'      <- chainRenameFilter r lyt
    return $ PrimVal q lyt'
last _ = $impossible

index ::  Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
index (ValueVector qs (Nest qi lyti)) (PrimVal i _) = do
    one       <- literal intT (VLInt 1)
    i'        <- vlBinExpr (L.SBNumOp L.Add) i one
    -- Use the unboxing rename vector
    (_, _, r) <- vlSelectPos qs (L.SBRelOp L.Eq) i'
    (qu, ri)  <- vlUnbox r qi
    lyti'     <- chainRenameFilter ri lyti
    return $ ValueVector qu lyti'
index (ValueVector qs lyt) (PrimVal i _) = do
    one       <- literal intT (VLInt 1)
    i'        <- vlBinExpr (L.SBNumOp L.Add) i one
    (q, r, _) <- vlSelectPos qs (L.SBRelOp L.Eq) i'
    lyt'      <- chainRenameFilter r lyt
    return $ PrimVal q lyt'
index _ _ = $impossible

append ::  Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
append = appendVec

-- FIXME looks fishy, there should be an unboxing join.
the ::  Shape VLDVec -> Build VL (Shape VLDVec)
the (ValueVector d lyt@(Nest _ _)) = do
    (_, prop, _)   <- vlSelectPos1 d (L.SBRelOp L.Eq) 1
    (Nest q' lyt') <- chainRenameFilter prop lyt
    return $ ValueVector q' lyt'
the (ValueVector d lyt) = do
    (q', prop, _) <- vlSelectPos1 d (L.SBRelOp L.Eq) 1
    lyt'          <- chainRenameFilter prop lyt
    return $ PrimVal q' lyt'
the _ = $impossible

reverse ::  Shape VLDVec -> Build VL (Shape VLDVec)
reverse (ValueVector d lyt) = do
    (d', p) <- vlReverse d
    lyt'    <- chainReorder p lyt
    return (ValueVector d' lyt')
reverse _ = $impossible

tail ::  Shape VLDVec -> Build VL (Shape VLDVec)
tail (ValueVector d lyt) = do
    p          <- literal intT (VLInt 1)
    (q', r, _) <- vlSelectPos d (L.SBRelOp L.Gt) p
    lyt'       <- chainRenameFilter r lyt
    return $ ValueVector q' lyt'
tail _ = $impossible

sort :: Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
sort (ValueVector q1 _) (ValueVector q2 lyt2) = do
    (v, p) <- vlSort q1 q2
    lyt2'  <- chainReorder p lyt2
    return $ ValueVector v lyt2'
sort _e1 _e2 = $impossible

group ::  Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
group (ValueVector q1 lyt1) (ValueVector q2 lyt2) = do
    (d, v, p) <- vlGroup q1 q2
    lyt2'     <- chainReorder p lyt2
    return $ ValueVector d (Pair lyt1 (Nest v lyt2') )
group _e1 _e2 = $impossible

length ::  Shape VLDVec -> Build VL (Shape VLDVec)
length q = do
    v' <- outer q
    v  <- vlAggr AggrCount v'
    return $ PrimVal v (InColumn 1)

cons ::  Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
cons q1@(PrimVal _ _) q2@(ValueVector _ _) = do
    n <- singletonAtom q1
    appendVec n q2
cons q1 q2 = do
    n <- singletonVec q1
    appendVec n q2

restrict ::  Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
restrict(ValueVector q1 lyt) (ValueVector q2 (InColumn 1)) = do
    (v, p) <- vlRestrict (Column 1) q1 q2
    lyt'   <- chainRenameFilter p lyt
    return $ ValueVector v lyt'
restrict e1 e2 = error $ "restrict: Can't construct restrict node " ++ show e1 ++ " " ++ show e2

combine ::  Shape VLDVec -> Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
combine (ValueVector qb (InColumn 1)) (ValueVector q1 lyt1) (ValueVector q2 lyt2) = do
    (v, p1, p2) <- vlCombine qb q1 q2
    lyt1'       <- renameOuter' p1 lyt1
    lyt2'       <- renameOuter' p2 lyt2
    lyt'        <- appendLayout lyt1' lyt2'
    return $ ValueVector v lyt'
combine _ _ _ = $impossible

dist ::  Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
dist (PrimVal q lyt) q2 = do
    o      <- outer q2
    (v, p) <- vlDistPrim q o
    lyt'   <- chainReorder p lyt
    return $ ValueVector v lyt'
dist (ValueVector q lyt) q2 = do
    o      <- outer q2
    (d, p) <- vlDistDesc q o

    -- The outer vector does not have columns, it only describes the
    -- shape.
    o'     <- vlProject o []
    lyt'   <- chainReorder p lyt
    return $ ValueVector o' (Nest d lyt')

aggr :: (Expr -> AggrFun) -> Shape VLDVec -> Build VL (Shape VLDVec)
aggr afun (ValueVector q (InColumn 1)) =
    PrimVal <$> vlAggr (afun (Column 1)) q <*> (pure $ InColumn 1)
aggr _ _ = $impossible


ifList ::  Shape VLDVec -> Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
ifList (PrimVal qb _) (ValueVector q1 lyt1) (ValueVector q2 lyt2) = do
    (d1', _)  <- vlDistPrim qb q1
    (d1, p1)  <- vlRestrict (Column 1) q1 d1'
    qb'       <- vlUnExpr (L.SUBoolOp L.Not) qb
    (d2', _)  <- vlDistPrim qb' q2
    (d2, p2)  <- vlRestrict (Column 1) q2 d2'
    lyt1'     <- renameOuter' p1 lyt1
    lyt2'     <- renameOuter' p2 lyt2
    lyt'      <- appendLayout lyt1' lyt2'
    (d, _, _) <- vlAppend d1 d2
    return $ ValueVector d lyt'
ifList qb (PrimVal q1 lyt1) (PrimVal q2 lyt2) = do
    (ValueVector q lyt) <- ifList qb (ValueVector q1 lyt1) (ValueVector q2 lyt2)
    return $ PrimVal q lyt
ifList _ _ _ = $impossible

pair ::  Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
pair (PrimVal q1 lyt1) (PrimVal q2 lyt2) = do
    q <- vlZip q1 q2
    let lyt = zipLayout lyt1 lyt2
    return $ PrimVal q lyt
pair (ValueVector q1 lyt1) (ValueVector q2 lyt2) = do
    d   <- vlLit L.PossiblyEmpty [] [[VLInt 1, VLInt 1]]
    q1' <- vlUnsegment q1
    q2' <- vlUnsegment q2
    let lyt = zipLayout (Nest q1' lyt1) (Nest q2' lyt2)
    return $ PrimVal d lyt
pair (ValueVector q1 lyt1) (PrimVal q2 lyt2) = do
    q1' <- vlUnsegment q1
    let lyt = zipLayout (Nest q1' lyt1) lyt2
    return $ PrimVal q2 lyt
pair (PrimVal q1 lyt1) (ValueVector q2 lyt2) = do
    q2' <- vlUnsegment q2
    let lyt = zipLayout lyt1 (Nest q2' lyt2)
    return $ PrimVal q1 lyt

fst ::  Shape VLDVec -> Build VL (Shape VLDVec)
fst (PrimVal _q (Pair (Nest q lyt) _p2)) = return $ ValueVector q lyt
fst (PrimVal q (Pair p1 _p2)) = do
    let (p1', cols) = projectFromPos p1
    proj <- vlProject q (map Column cols)
    return $ PrimVal proj p1'
fst e1 = error $ "fstA: " ++ show e1

snd ::  Shape VLDVec -> Build VL (Shape VLDVec)
snd (PrimVal _q (Pair _p1 (Nest q lyt))) = return $ ValueVector q lyt
snd (PrimVal q (Pair _p1 p2)) = do
    let (p2', cols) = projectFromPos p2
    proj <- vlProject q (map Column cols)
    return $ PrimVal proj p2'
snd _ = $impossible

transpose :: Shape VLDVec -> Build VL (Shape VLDVec)
transpose (ValueVector _ (Nest qi lyt)) = do
    (qo', qi') <- vlTranspose qi
    return $ ValueVector qo' (Nest qi' lyt)
transpose _ = $impossible


reshape :: Integer -> Shape VLDVec -> Build VL (Shape VLDVec)
reshape n (ValueVector q lyt) = do
    (qo, qi) <- vlReshape n q
    return $ ValueVector qo (Nest qi lyt)
reshape _ _ = $impossible

concat :: Shape VLDVec -> Build VL (Shape VLDVec)
concat (ValueVector _ (Nest q lyt)) = ValueVector <$> vlUnsegment q <*> pure lyt
concat e                            = error $ "Not supported by concatV: " ++ show e


--------------------------------------------------------------------------------
-- Construction of lifted primitives

restrictL :: Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
restrictL (ValueVector qo (Nest qi lyt)) (ValueVector _ (Nest qb (InColumn 1))) = do
    ValueVector qi' lyt' <- restrict (ValueVector qi lyt) (ValueVector qb (InColumn 1))
    return $ ValueVector qo (Nest qi' lyt')
restrictL _                              _                                      = 
    $impossible

combineL :: Shape VLDVec -> Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
combineL (ValueVector qo (Nest qb (InColumn 1)))
         (ValueVector _ (Nest qi1 lyt1)) 
         (ValueVector _ (Nest qi2 lyt2)) = do
    ValueVector qi' lyt' <- combine (ValueVector qb (InColumn 1)) (ValueVector qi1 lyt1) (ValueVector qi2 lyt2)
    return $ ValueVector qo (Nest qi' lyt')
combineL _ _ _ = $impossible

zipL ::  Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
zipL (ValueVector d1 (Nest q1 lyt1)) (ValueVector _ (Nest q2 lyt2)) = do
    (q', r1, r2) <- vlZipS q1 q2
    lyt1'        <- chainRenameFilter r1 lyt1
    lyt2'        <- chainRenameFilter r2 lyt2
    return $ ValueVector d1 (Nest q' $ zipLayout lyt1' lyt2')
zipL _ _ = $impossible

cartProductL :: Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
cartProductL (ValueVector d1 (Nest q1 lyt1)) (ValueVector _ (Nest q2 lyt2)) = do
    (q', p1, p2) <- vlCartProductS q1 q2
    lyt1'        <- chainReorder p1 lyt1
    lyt2'        <- chainReorder p2 lyt2
    return $ ValueVector d1 (Nest q' $ zipLayout lyt1' lyt2')
cartProductL _ _ = $impossible

nestProductL :: Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
nestProductL (ValueVector qd1 (Nest qv1 lyt1)) (ValueVector _qd2 (Nest qv2 lyt2)) = do
    (qj, qp2) <- vlNestProductS qv1 qv2
    lyt2'     <- chainReorder qp2 lyt2
    let lytJ  = zipLayout lyt1 lyt2'
    return $ ValueVector qd1 (Nest qv1 (Pair lyt1 (Nest qj lytJ)))
nestProductL _ _ = $impossible

thetaJoinL :: L.JoinPredicate L.JoinExpr -> Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
thetaJoinL joinPred (ValueVector d1 (Nest q1 lyt1)) (ValueVector _ (Nest q2 lyt2)) = do
    (q', p1, p2) <- vlThetaJoinS joinPred q1 q2
    lyt1'        <- chainReorder p1 lyt1
    lyt2'        <- chainReorder p2 lyt2
    return $ ValueVector d1 (Nest q' $ zipLayout lyt1' lyt2')
thetaJoinL _ _ _ = $impossible

-- △^L :: [[a]] -> [[b]] -> [[(a, [(a, b)])]]

-- For the unlifted nestjoin, we could segment the left (outer) input
-- and then use the regular thetajoin implementation. This trick does
-- not work here, as the lifted thetajoin joins on the
-- descriptors. Therefore, we have to 'segment' **after** the join,
-- i.e. use the left input positions as descriptors
nestJoinL :: L.JoinPredicate L.JoinExpr -> Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
nestJoinL joinPred (ValueVector qd1 (Nest qv1 lyt1)) (ValueVector _qd2 (Nest qv2 lyt2)) = do
    (qj, qp2) <- vlNestJoinS joinPred qv1 qv2
    lyt2'     <- chainReorder qp2 lyt2
    let lytJ  = zipLayout lyt1 lyt2'
    return $ ValueVector qd1 (Nest qv1 (Pair lyt1 (Nest qj lytJ)))
nestJoinL _ _ _ = $impossible

semiJoinL :: L.JoinPredicate L.JoinExpr -> Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
semiJoinL joinPred (ValueVector d1 (Nest q1 lyt1)) (ValueVector _ (Nest q2 _)) = do
    (qj, r) <- vlSemiJoinS joinPred q1 q2
    lyt1'   <- chainRenameFilter r lyt1
    return $ ValueVector d1 (Nest qj lyt1')
semiJoinL _ _ _ = $impossible

antiJoinL :: L.JoinPredicate L.JoinExpr -> Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
antiJoinL joinPred (ValueVector d1 (Nest q1 lyt1)) (ValueVector _ (Nest q2 _)) = do
    (qj, r) <- vlAntiJoinS joinPred q1 q2
    lyt1'   <- chainRenameFilter r lyt1
    return $ ValueVector d1 (Nest qj lyt1')
antiJoinL _ _ _ = $impossible



nubL ::  Shape VLDVec -> Build VL (Shape VLDVec)
nubL (ValueVector d (Nest q lyt)) =  ValueVector d <$> (Nest <$> vlUniqueS q <*> pure lyt)
nubL _ = $impossible

numberL ::  Shape VLDVec -> Build VL (Shape VLDVec)
numberL (ValueVector d (Nest q lyt)) =
    ValueVector d <$> (Nest <$> vlNumberS q
                            <*> (pure $ zipLayout lyt (InColumn 1)))
numberL _ = $impossible

initL ::  Shape VLDVec -> Build VL (Shape VLDVec)
initL (ValueVector qs (Nest q lyt)) = do
    is         <- vlAggrS AggrCount qs q
    (q', r, _) <- vlSelectPosS q (L.SBRelOp L.Lt) is
    lyt'       <- chainRenameFilter r lyt
    return $ ValueVector qs (Nest q' lyt')
initL _ = $impossible

lastL ::  Shape VLDVec -> Build VL (Shape VLDVec)
lastL (ValueVector d (Nest qs lyt@(Nest _ _))) = do
    is          <- vlAggrS AggrCount d qs
    (qs', r, _) <- vlSelectPosS qs (L.SBRelOp L.Eq) is
    lyt'        <- chainRenameFilter r lyt
    re          <- vlUnboxRename qs'
    ValueVector d <$> renameOuter' re lyt'
lastL (ValueVector d (Nest qs lyt)) = do
    is          <- vlAggrS AggrCount d qs
    (qs', r, _) <- vlSelectPosS qs (L.SBRelOp L.Eq) is
    lyt'        <- chainRenameFilter r lyt
    re          <- vlUnboxRename d
    renameOuter re (ValueVector qs' lyt')
lastL _ = $impossible

indexL ::  Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
indexL (ValueVector d (Nest qs (Nest qi lyti))) (ValueVector is (InColumn 1)) = do
    one       <- literal intT (VLInt 1)
    (ones, _) <- vlDistPrim one is
    is'       <- vlBinExpr (L.SBNumOp L.Add) is ones
    (_, _, u) <- vlSelectPosS qs (L.SBRelOp L.Eq) is'
    (qu, ri)  <- vlUnbox u qi
    lyti'     <- chainRenameFilter ri lyti
    return $ ValueVector d (Nest qu lyti')
indexL (ValueVector d (Nest qs lyt)) (ValueVector is (InColumn 1)) = do
    one         <- literal intT (VLInt 1)
    (ones, _)   <- vlDistPrim one is
    is'         <- vlBinExpr (L.SBNumOp L.Add) is ones
    (qs', r, _) <- vlSelectPosS qs (L.SBRelOp L.Eq) is'
    lyt'        <- chainRenameFilter r lyt
    re          <- vlUnboxRename d
    renameOuter re (ValueVector qs' lyt')
indexL _ _ = $impossible

appendL ::  Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
appendL (ValueVector d lyt1) (ValueVector _ lyt2) = do
    ValueVector d <$> appendLayout lyt1 lyt2
appendL _ _ = $impossible

reverseL ::  Shape VLDVec -> Build VL (Shape VLDVec)
reverseL (ValueVector d (Nest d1 lyt)) = do
    (d1', p) <- vlReverseS d1
    lyt'     <- chainReorder p lyt
    return (ValueVector d (Nest d1' lyt'))
reverseL _ = $impossible

theL ::  Shape VLDVec -> Build VL (Shape VLDVec)
theL (ValueVector d (Nest q lyt)) = do
    (v, p2, _) <- vlSelectPos1S q (L.SBRelOp L.Eq) 1
    prop       <- vlUnboxRename d
    lyt'       <- chainRenameFilter p2 lyt
    v'         <- vlPropRename prop v
    return $ ValueVector v' lyt'
theL _ = $impossible

tailL ::  Shape VLDVec -> Build VL (Shape VLDVec)
tailL (ValueVector d (Nest q lyt)) = do
    one        <- literal intT (VLInt 1)
    (p, _)     <- vlDistPrim one d
    (v, p2, _) <- vlSelectPosS q (L.SBRelOp L.Gt) p
    lyt'       <- chainRenameFilter p2 lyt
    return $ ValueVector d (Nest v lyt')
tailL _ = $impossible

sortL ::  Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
sortL (ValueVector _ (Nest v1 _)) (ValueVector d2 (Nest v2 lyt2)) = do
    (v, p) <- vlSort v1 v2
    lyt2'  <- chainReorder p lyt2
    return $ ValueVector d2 (Nest v lyt2')
sortL _ _ = $impossible

groupL ::  Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
groupL (ValueVector _ (Nest v1 lyt1)) (ValueVector d2 (Nest v2 lyt2)) = do
    (d, v, p) <- vlGroup v1 v2
    lyt2'     <- chainReorder p lyt2
    return $ ValueVector d2 (Nest d (Pair lyt1 (Nest v lyt2')))
groupL _ _ = $impossible

concatL ::  Shape VLDVec -> Build VL (Shape VLDVec)
concatL (ValueVector d (Nest d' vs)) = do
    p   <- vlUnboxRename d'
    vs' <- renameOuter' p vs
    return $ ValueVector d vs'
concatL _ = $impossible

lengthL ::  Shape VLDVec -> Build VL (Shape VLDVec)
lengthL (ValueVector q (Nest qi _)) = do
    ls <- vlAggrS AggrCount q qi
    return $ ValueVector ls (InColumn 1)
lengthL s = trace (show s) $ $impossible

consL ::  Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
consL (ValueVector q1 lyt1) (ValueVector q2 (Nest qi lyt2)) = do
    s           <- vlSegment q1
    (v, p1, p2) <- vlAppendS s qi
    lyt1'       <- renameOuter' p1 lyt1
    lyt2'       <- renameOuter' p2 lyt2
    lyt'        <- appendLayout lyt1' lyt2'
    return $ ValueVector q2 (Nest v lyt')
consL _ _ = $impossible


outer ::  Shape VLDVec -> Build VL VLDVec
outer (PrimVal _ _)            = $impossible
outer (ValueVector q _)        = return q

aggrL :: (Expr -> AggrFun) -> Shape VLDVec -> Build VL (Shape VLDVec)
aggrL afun (ValueVector d (Nest q (InColumn 1))) = do
    qr <- vlAggrS (afun (Column 1)) d q
    return $ ValueVector qr (InColumn 1)
aggrL _ _ = $impossible


mapEnv :: (Shape VLDVec -> Build VL (Shape VLDVec))
       -> [(String, Shape VLDVec)]
       -> Build VL [(String, Shape VLDVec)]
mapEnv f  ((x, p):xs) = do
    p'  <- f p
    xs' <- mapEnv f xs
    return $ (x, p') : xs'
mapEnv _f []          = return []

distL ::  Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
distL (ValueVector q1 lyt1) (ValueVector d (Nest q2 lyt2)) = do
    (qa, p)             <- vlAlign q1 q2
    lyt1'               <- chainReorder p lyt1
    let lyt             = zipLayout lyt1' lyt2
    ValueVector qf lytf <- fstL $ ValueVector qa lyt
    return $ ValueVector d (Nest qf lytf)
distL _e1 _e2 = error $ "distL: Should not be possible" ++ show _e1 ++ "\n" ++ show _e2


pairL ::  Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
pairL (ValueVector q1 lyt1) (ValueVector q2 lyt2) = do
    q <- vlZip q1 q2
    let lyt = zipLayout lyt1 lyt2
    return $ ValueVector q lyt
pairL _ _ = $impossible

fstL ::  Shape VLDVec -> Build VL (Shape VLDVec)
fstL (ValueVector q (Pair p1 _p2)) = do
    let(p1', cols) = projectFromPos p1
    proj <- vlProject q (map Column cols)
    return $ ValueVector proj p1'
fstL s = error $ "fstL: " ++ show s

sndL ::  Shape VLDVec -> Build VL (Shape VLDVec)
sndL (ValueVector q (Pair _p1 p2)) = do
    let (p2', cols) = projectFromPos p2
    proj <- vlProject q (map Column cols)
    return $ ValueVector proj p2'
sndL s = trace (show s) $ $impossible

transposeL :: Shape VLDVec -> Build VL (Shape VLDVec)
transposeL (ValueVector qo (Nest qm (Nest qi lyt))) = do
    (qm', qi') <- vlTransposeS qm qi
    return $ ValueVector qo (Nest qm' (Nest qi' lyt))
transposeL _ = $impossible

reshapeL :: Integer -> Shape VLDVec -> Build VL (Shape VLDVec)
reshapeL n (ValueVector qo (Nest qi lyt)) = do
    (qm, qi') <- vlReshapeS n qi
    return $ ValueVector qo (Nest qm (Nest qi' lyt))
reshapeL _ _ = $impossible

projectFromPos :: Layout VLDVec -> (Layout VLDVec , [DBCol])
projectFromPos = (\(x,y,_) -> (x,y)) . (projectFromPosWork 1)
  where
    projectFromPosWork :: Int -> Layout VLDVec -> (Layout VLDVec, [DBCol], Int)
    projectFromPosWork c (InColumn i) = (InColumn c, [i], c + 1)
    projectFromPosWork c (Nest q l)   = (Nest q l, [], c)
    projectFromPosWork c (Pair p1 p2) = let (p1', cols1, c') = projectFromPosWork c p1
                                            (p2', cols2, c'') = projectFromPosWork c' p2
                                        in (Pair p1' p2', cols1 ++ cols2, c'')

singletonVec ::  Shape VLDVec -> Build VL (Shape VLDVec)
singletonVec (ValueVector q lyt) = do
    VLDVec d <- vlSingletonDescr
    return $ ValueVector (VLDVec d) (Nest q lyt)
singletonVec _ = $impossible

singletonAtom ::  Shape VLDVec -> Build VL (Shape VLDVec)
singletonAtom (PrimVal q1 lyt) = return $ ValueVector q1 lyt
singletonAtom _ = $impossible

--------------------------------------------------------------------------------
-- Construction of base tables and literal tables

dbTable ::  String -> [L.Column] -> L.TableHints -> Build VL (Shape VLDVec)
dbTable n cs ks = do
    t <- vlTableRef n (map (mapSnd typeToRowType) cs) ks
    return $ ValueVector t (foldr1 Pair [InColumn i | i <- [1..P.length cs]])

mkLiteral ::  Type -> L.Val -> Build VL (Shape VLDVec)
mkLiteral t@(ListT _) (L.ListV es) = do
    ((descHd, descV), lyt, _) <- toPlan (mkDescriptor [P.length es]) t 1 es
    let emptinessFlag = case es of
          []    -> L.PossiblyEmpty
          _ : _ -> L.NonEmpty
    litNode <- vlLit emptinessFlag (P.reverse descHd) $ map P.reverse descV
    return $ ValueVector litNode lyt
mkLiteral (FunT _ _) _  = $impossible
mkLiteral t e           = do
    ((descHd, [descV]), layout, _) <- toPlan (mkDescriptor [1]) (ListT t) 1 [e]
    litNode <- vlLit L.NonEmpty (P.reverse descHd) [(P.reverse descV)]
    return $ PrimVal litNode layout

type Table = ([Type], [[VLVal]])

-- FIXME Check if inner list literals are nonempty and flag VL
-- literals appropriately.
toPlan ::  Table -> Type -> Int -> [L.Val] -> Build VL (Table, Layout VLDVec, Int)
toPlan (descHd, descV) (ListT t) c es =
    case t of
        PairT t1 t2 -> do
            let (e1s, e2s) = unzip $ map splitVal es
            (desc', l1, c') <- toPlan (descHd, descV) (ListT t1) c e1s
            (desc'', l2, c'') <- toPlan desc' (ListT t2) c' e2s
            return (desc'', Pair l1 l2, c'')

        ListT _ -> do
            let vs = map fromListVal es
            let d = mkDescriptor $ map P.length vs
            ((hd, vs'), l, _) <- toPlan d t 1 (P.concat vs)
            n <- vlLit L.PossiblyEmpty (P.reverse hd) (map P.reverse vs')
            return ((descHd, descV), Nest n l, c)

        FunT _ _ -> $impossible

        _ -> let (hd, vs) = mkColumn t es
             in return ((hd:descHd, zipWith (:) vs descV), (InColumn c), c + 1)

toPlan _ (FunT _ _) _ _ = $impossible
toPlan (descHd, descV) t c v =
    let (hd, v') = mkColumn t v
    in return $ ((hd:descHd, zipWith (:) v' descV), (InColumn c), c + 1)

literal :: Type -> VLVal -> Build VL VLDVec
literal t v = vlLit L.NonEmpty [t] [[VLInt 1, VLInt 1, v]]

fromListVal :: L.Val -> [L.Val]
fromListVal (L.ListV es) = es
fromListVal _            = $impossible

splitVal :: L.Val -> (L.Val, L.Val)
splitVal (L.PairV e1 e2) = (e1, e2)
splitVal _               = error $ "splitVal: Not a tuple"

mkColumn :: Type -> [L.Val] -> (Type, [VLVal])
mkColumn t vs = (t, [pVal v | v <- vs])

mkDescriptor :: [Int] -> Table
mkDescriptor lengths =
    let header = []
        body = map (\(d, p) -> [VLInt $ fromInteger p, VLInt $ fromInteger d])
               $ P.zip (P.concat [ replicate l p | (p, l) <- P.zip [1..] lengths] ) [1..]
    in (header, body)

--------------------------------------------------------------------------------
-- Helper functions for layouts

zipLayout :: Layout VLDVec -> Layout VLDVec -> Layout VLDVec
zipLayout l1 l2 = let offSet = columnsInLayout l1
                      l2' = incrementPositions offSet l2
                   in Pair l1 l2'

incrementPositions :: Int -> Layout VLDVec -> Layout VLDVec
incrementPositions i (InColumn n)  = InColumn $ n + i
incrementPositions _i v@(Nest _ _) = v
incrementPositions i (Pair l1 l2)  = Pair (incrementPositions i l1) (incrementPositions i l2)

--------------------------------------------------------------------------------
-- Compile-time operations that implement higher-lifted primitives.

-- | Remove the 'n' outer layers of nesting from a nested list
-- (Prins/Palmer: 'extract').
qConcat :: F.Nat -> Shape VLDVec -> Shape VLDVec
qConcat F.Zero _ = $impossible
qConcat (F.Succ F.Zero) (ValueVector _ (Nest q lyt)) = ValueVector q lyt
qConcat (F.Succ n)      (ValueVector _ lyt)          = extractInnerVec n lyt
qConcat _               _                            = $impossible

extractInnerVec :: F.Nat -> Layout VLDVec -> Shape VLDVec
extractInnerVec (F.Succ F.Zero) (Nest _ (Nest q lyt)) = ValueVector q lyt
extractInnerVec (F.Succ n)      (Nest _ lyt)          = extractInnerVec n lyt
extractInnerVec _               _                     = $impossible

-- | Prepend the 'n' outer layers of nesting from the first input to
-- the second input (Prins/Palmer: 'insert').
unconcat :: F.Nat -> Shape VLDVec -> Shape VLDVec -> Shape VLDVec
unconcat (F.Succ F.Zero) (ValueVector d _) (ValueVector vi lyti) =
    ValueVector d (Nest vi lyti)
unconcat (F.Succ n) (ValueVector d lyt) (ValueVector vi lyti)    = 
    ValueVector d (implantInnerVec n lyt vi lyti)
unconcat _          _                   _                        = 
    $impossible

implantInnerVec :: F.Nat -> Layout VLDVec -> VLDVec -> Layout VLDVec -> Layout VLDVec
implantInnerVec (F.Succ F.Zero) (Nest d _)   vi lyti = 
    Nest d $ Nest vi lyti
implantInnerVec (F.Succ n)      (Nest d lyt) vi lyti = 
    Nest d $ implantInnerVec n lyt vi lyti
implantInnerVec _          _            _  _         = 
    $impossible
