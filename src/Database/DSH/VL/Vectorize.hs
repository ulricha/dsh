{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE ParallelListComp #-}

-- | Vectorising constructor functions that implement FKL primitives
-- using VL operators.
module Database.DSH.VL.Vectorize where

import           Debug.Trace

import           Control.Applicative
import qualified Data.List                     as List
import qualified Data.List.NonEmpty            as N
import           Prelude                       hiding (reverse, zip)
import qualified Prelude                       as P

import           Database.Algebra.Dag.Build

import qualified Database.DSH.Common.Lang      as L
import           Database.DSH.Common.Nat
import           Database.DSH.Common.QueryPlan
import           Database.DSH.Common.Type
import           Database.DSH.Common.Impossible
import           Database.DSH.VL.Lang          (AggrFun (..), Expr (..), VL ())
import           Database.DSH.VL.Primitives
import           Database.DSH.Common.Vector

--------------------------------------------------------------------------------
-- Construction of not-lifted primitives

zip ::  Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
zip (VShape dv1 lyt1) (VShape dv2 lyt2) = do
    (dv, fv1, fv2) <- vlZip dv1 dv2
    lyt1'          <- filterLayout fv1 lyt1
    lyt2'          <- filterLayout fv2 lyt2
    return $ VShape dv $ LTuple [lyt1', lyt2']
zip _ _ = $impossible

cartProduct :: Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
cartProduct (VShape dv1 lyt1) (VShape dv2 lyt2) = do
    (dv, rv1, rv2) <- vlCartProduct dv1 dv2
    lyt1'          <- repLayout rv1 lyt1
    lyt2'          <- repLayout rv2 lyt2
    return $ VShape dv $ LTuple [lyt1', lyt2']
cartProduct _ _ = $impossible

nestProduct :: Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
nestProduct (VShape dv1 lyt1) (VShape dv2 lyt2) = do
  (dvi, rv1, rv2) <- vlNestProduct dv1 dv2
  lyt1'           <- repLayout rv1 lyt1
  lyt2'           <- repLayout rv2 lyt2
  return $ VShape dv1 (LTuple [lyt1, LNest dvi (LTuple [lyt1', lyt2'])])
nestProduct _ _ = $impossible

thetaJoin :: L.JoinPredicate L.JoinExpr -> Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
thetaJoin joinPred (VShape dv1 lyt1) (VShape dv2 lyt2) = do
    (dv, rv1, rv2) <- vlThetaJoin joinPred dv1 dv2
    lyt1'          <- repLayout rv1 lyt1
    lyt2'          <- repLayout rv2 lyt2
    return $ VShape dv $ LTuple [lyt1', lyt2']
thetaJoin _ _ _ = $impossible

nestJoin :: L.JoinPredicate L.JoinExpr -> Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
nestJoin joinPred (VShape dv1 lyt1) (VShape dv2 lyt2) = do
    (dv, rv1, rv2) <- vlNestJoin joinPred dv1 dv2
    lyt1'          <- repLayout rv1 lyt1
    lyt2'          <- repLayout rv2 lyt2
    return $ VShape dv1 (LTuple [lyt1, LNest dv (LTuple [lyt1', lyt2'])])
nestJoin _ _ _ = $impossible

semiJoin :: L.JoinPredicate L.JoinExpr -> Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
semiJoin joinPred (VShape dv1 lyt1) (VShape dv2 _) = do
    (dv, fv) <- vlSemiJoin joinPred dv1 dv2
    lyt1'    <- filterLayout fv lyt1
    return $ VShape dv lyt1'
semiJoin _ _ _ = $impossible

antiJoin :: L.JoinPredicate L.JoinExpr -> Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
antiJoin joinPred (VShape dv1 lyt1) (VShape dv2 _) = do
    (dv, fv) <- vlAntiJoin joinPred dv1 dv2
    lyt1'    <- filterLayout fv lyt1
    return $ VShape dv lyt1'
antiJoin _ _ _ = $impossible

nub ::  Shape VLDVec -> Build VL (Shape VLDVec)
nub (VShape dv lyt) = VShape <$> vlUniqueS dv <*> pure lyt
nub _ = $impossible

number ::  Shape VLDVec -> Build VL (Shape VLDVec)
number (VShape q lyt) =
    VShape <$> vlNumber q <*> (pure $ LTuple [lyt, LCol])
number _ = $impossible

init ::  Shape VLDVec -> Build VL (Shape VLDVec)
init (VShape q lyt) = do
    i          <- vlAggr AggrCount q
    (q', r, _) <- vlSelectPos q (L.SBRelOp L.Lt) i
    lyt'       <- filterLayout r lyt
    return $ VShape q' lyt'
init _ = $impossible

last ::  Shape VLDVec -> Build VL (Shape VLDVec)
last (VShape qs lyt@(LNest _ _)) = do
    i             <- vlAggr AggrCount qs
    (q, r, _)     <- vlSelectPos qs (L.SBRelOp L.Eq) i
    LNest qr lyt' <- filterLayout r lyt
    re            <- vlUnboxRename q
    VShape <$> vlAppKey re qr <*> pure lyt'
last (VShape qs lyt) = do
    i         <- vlAggr AggrCount qs
    (q, r, _) <- vlSelectPos qs (L.SBRelOp L.Eq) i
    lyt'      <- filterLayout r lyt
    return $ SShape q lyt'
last _ = $impossible

index ::  Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
index (VShape qs (LNest qi lyti)) (SShape i _) = do
    one       <- literal PIntT (L.IntV 1)
    i'        <- vlBinExpr (L.SBNumOp L.Add) i one
    -- Use the unboxing rename vector
    (_, _, r) <- vlSelectPos qs (L.SBRelOp L.Eq) i'
    (qu, ri)  <- vlUnboxNested r qi
    lyti'     <- rekeyLayout ri lyti
    return $ VShape qu lyti'
index (VShape qs lyt) (SShape i _) = do
    one       <- literal PIntT (L.IntV 1)
    i'        <- vlBinExpr (L.SBNumOp L.Add) i one
    (q, r, _) <- vlSelectPos qs (L.SBRelOp L.Eq) i'
    lyt'      <- filterLayout r lyt
    return $ SShape q lyt'
index _ _ = $impossible

append ::  Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
append (VShape dv1 lyt1) (VShape dv2 lyt2) = do
    -- Append the current vectors
    (dv12, kv1, kv2) <- vlAppend dv1 dv2
    -- Propagate position changes to descriptors of any inner vectors
    lyt1'       <- rekeyLayout kv1 lyt1
    lyt2'       <- rekeyLayout kv2 lyt2
    -- Append the layouts, i.e. actually append all inner vectors
    lyt'        <- appendLayout lyt1' lyt2'
    return $ VShape dv12 lyt'
append _ _ = $impossible

-- FIXME looks fishy, there should be an unboxing join.
the ::  Shape VLDVec -> Build VL (Shape VLDVec)
the (VShape d lyt@(LNest _ _)) = do
    (_, prop, _)  <- vlSelectPos1 d (L.SBRelOp L.Eq) 1
    LNest q' lyt' <- filterLayout prop lyt
    return $ VShape q' lyt'
the (VShape d lyt) = do
    (q', prop, _) <- vlSelectPos1 d (L.SBRelOp L.Eq) 1
    lyt'          <- filterLayout prop lyt
    return $ SShape q' lyt'
the _ = $impossible

reverse ::  Shape VLDVec -> Build VL (Shape VLDVec)
reverse (VShape dv lyt) = do
    (dv', sv) <- vlReverse dv
    lyt'      <- sortLayout sv lyt
    return (VShape dv' lyt')
reverse _ = $impossible

tail ::  Shape VLDVec -> Build VL (Shape VLDVec)
tail (VShape d lyt) = do
    p          <- literal PIntT (L.IntV 1)
    (q', r, _) <- vlSelectPos d (L.SBRelOp L.Gt) p
    lyt'       <- filterLayout r lyt
    return $ VShape q' lyt'
tail _ = $impossible

sort :: Shape VLDVec -> Build VL (Shape VLDVec)
sort (VShape dv (LTuple [xl, sl])) = do
    let leftWidth  = columnsInLayout xl
        rightWidth = columnsInLayout sl

        sortExprs = map Column [leftWidth+1..leftWidth+rightWidth]

    -- Sort by all sorting columns from the right tuple component
    (dv', sv) <- vlSort sortExprs dv

    -- After sorting, discard the sorting criteria columns
    dv''      <- vlProject (map Column [1..leftWidth]) dv'
    xl'       <- sortLayout sv xl
    return $ VShape dv'' xl'
sort _e1 = $impossible

-- | The right input contains the grouping columns.
group ::  Shape VLDVec -> Build VL (Shape VLDVec)
group (VShape dv (LTuple [lyt1, lyt2])) = do
    let leftWidth  = columnsInLayout lyt1
        rightWidth = columnsInLayout lyt2

        groupExprs = map Column [leftWidth+1..leftWidth+rightWidth]

    (dvo, dvi, sv) <- vlGroup groupExprs dv

    -- Discard the grouping columns in the inner vector
    dvi'           <- vlProject (map Column [1..leftWidth]) dvi

    lyt1'          <- sortLayout sv lyt1
    return $ VShape dvo (LTuple [lyt2, LNest dvi' lyt1'])
group _e1 = $impossible

length_ ::  Shape VLDVec -> Build VL (Shape VLDVec)
length_ (VShape q _) = do
    v  <- vlAggr AggrCount q
    return $ SShape v LCol
length_ _ = $impossible

restrict ::  Shape VLDVec -> Build VL (Shape VLDVec)
restrict (VShape dv (LTuple [l, LCol])) = do
    -- The right input vector has only one boolean column which
    -- defines wether the tuple at the same position in the left input
    -- is preserved.
    let leftWidth = columnsInLayout l
        predicate = Column $ leftWidth + 1

    -- Filter the vector according to the boolean column
    (dv', fv) <- vlSelect predicate dv

    -- After the selection, discard the boolean column from the right
    dv''      <- vlProject (map Column [1..leftWidth]) dv'

    -- Filter any inner vectors
    l'        <- filterLayout fv l
    return $ VShape dv'' l'
restrict e1 = trace (show e1) $ $impossible

combine ::  Shape VLDVec -> Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
combine (VShape dvb LCol) (VShape dv1 lyt1) (VShape dv2 lyt2) = do
    (dv, kv1, kv2) <- vlCombine dvb dv1 dv2
    lyt1'          <- rekeyLayout kv1 lyt1
    lyt2'          <- rekeyLayout kv2 lyt2
    lyt'           <- appendLayout lyt1' lyt2'
    return $ VShape dv lyt'
combine l1 l2 l3 = trace (show l1 ++ " " ++ show l2 ++ " " ++ show l3) $ $impossible

-- | Distribute a single value in vector 'q2' over an arbitrary shape.
-- FIXME accepting a scalar shape makes no sense here. we can only distribute over a list.
distSingleton :: Shape VLDVec -> VLDVec -> Layout VLDVec -> Build VL (Shape VLDVec)
distSingleton shape1 dv2 lyt2 = do
    let (shapeCon, dv1, lyt1) = unwrapShape shape1

        leftWidth  = columnsInLayout lyt1
        rightWidth = columnsInLayout lyt2
        proj       = map Column [leftWidth+1..leftWidth+rightWidth]

    (dv, _, rv) <- dv1 `vlCartProduct` dv2
    dv'         <- vlProject proj dv

    lyt'        <- repLayout rv lyt2
    return $ shapeCon dv' lyt'

dist ::  Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
-- Distributing a single value is implemented using a cartesian
-- product. After the product, we discard columns from the vector that
-- we distributed over. Vectors are swapped because CartProduct uses
-- the descriptor of its left input and that is what we want.
dist (SShape q lyt) v = distSingleton v q lyt
dist (VShape dv lyt) (VShape dvo lyto) = do
    let leftWidth  = columnsInLayout lyto
        rightWidth = columnsInLayout lyt
        innerProj  = map Column [leftWidth+1..leftWidth+rightWidth]

    (prodVec, _, rv) <- vlNestProduct dvo dv
    innerVec         <- vlProject innerProj prodVec

    -- The outer vector does not have columns, it only describes the
    -- shape.
    outerVec         <- vlProject [] dvo

    -- Replicate any inner vectors
    lyt'             <- repLayout rv lyt

    return $ VShape outerVec (LNest innerVec lyt')
dist _ _ = $impossible

aggr :: (Expr -> AggrFun) -> Shape VLDVec -> Build VL (Shape VLDVec)
aggr afun (VShape q LCol) =
    SShape <$> vlAggr (afun (Column 1)) q <*> pure LCol
aggr _ _ = $impossible

ifList ::  Shape VLDVec -> Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
ifList (SShape qb lytb) (VShape q1 lyt1) (VShape q2 lyt2) = do
    let leftWidth = columnsInLayout lyt1
        predicate = Column $ leftWidth + 1

    VShape trueSelVec _  <- distSingleton (VShape q1 lyt1) qb lytb
    (trueVec, truefv)    <- vlSelect predicate
                                  =<< vlAlign q1 trueSelVec
    trueVec'             <- vlProject (map Column [1..leftWidth]) trueVec

    let predicate' = UnApp (L.SUBoolOp L.Not) predicate

    VShape falseSelVec _ <- distSingleton (VShape q2 lyt2) qb lytb
    (falseVec, falsefv)  <- vlSelect predicate'
                            =<< vlAlign q2 falseSelVec
    falseVec'            <- vlProject (map Column [1..leftWidth]) falseVec

    lyt1'                <- filterLayout truefv lyt1
    lyt2'                <- filterLayout falsefv lyt2
    lyt'                 <- appendLayout lyt1' lyt2'

    (bothBranches, _, _) <- vlAppend trueVec' falseVec'

    return $ VShape bothBranches lyt'
ifList qb (SShape q1 lyt1) (SShape q2 lyt2) = do
    (VShape q lyt) <- ifList qb (VShape q1 lyt1) (VShape q2 lyt2)
    return $ SShape q lyt
ifList _ _ _ = $impossible

tuple :: [Shape VLDVec] -> Build VL (Shape VLDVec)
tuple shapes@(_ : _) = do
    (q, lyts) <- boxVectors shapes
    return $ SShape q (LTuple lyts)
tuple _ = $impossible

tupElem :: TupleIndex -> Shape VLDVec -> Build VL (Shape VLDVec)
tupElem i (SShape q (LTuple lyts)) =
    case lyts !! (tupleIndex i - 1) of
        LNest qi lyt -> return $ VShape qi lyt
        _            -> do
            let (lyt', cols) = projectColumns i lyts
            proj <- vlProject (map Column cols) q
            return $ SShape proj lyt'
tupElem _ _ = $impossible

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
concat _e                       = $impossible

--------------------------------------------------------------------------------
-- Construction of lifted primitives

restrictL :: Shape VLDVec -> Build VL (Shape VLDVec)
restrictL (VShape qo (LNest qi lyt)) = do
    VShape qi' lyt' <- restrict (VShape qi lyt)
    return $ VShape qo (LNest qi' lyt')
restrictL l1 = trace (show l1) $ $impossible

combineL :: Shape VLDVec -> Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
combineL (VShape qo (LNest qb LCol))
         (VShape _ (LNest qi1 lyt1))
         (VShape _ (LNest qi2 lyt2)) = do
    VShape qi' lyt' <- combine (VShape qb LCol) (VShape qi1 lyt1) (VShape qi2 lyt2)
    return $ VShape qo (LNest qi' lyt')
combineL _ _ _ = $impossible

zipL ::  Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
zipL (VShape d1 (LNest q1 lyt1)) (VShape _ (LNest q2 lyt2)) = do
    (q', r1, r2) <- vlZipS q1 q2
    lyt1'        <- filterLayout r1 lyt1
    lyt2'        <- filterLayout r2 lyt2
    return $ VShape d1 (LNest q' $ LTuple [lyt1', lyt2'])
zipL _ _ = $impossible

cartProductL :: Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
cartProductL (VShape dvo1 (LNest dvi1 lyt1)) (VShape _ (LNest dvi2 lyt2)) = do
    (dv, rv1, rv2) <- vlCartProductS dvi1 dvi2
    lyt1'        <- repLayout rv1 lyt1
    lyt2'        <- repLayout rv2 lyt2
    return $ VShape dvo1 (LNest dv $ LTuple [lyt1', lyt2'])
cartProductL _ _ = $impossible

nestProductL :: Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
nestProductL (VShape dvo1 (LNest dvi1 lyt1)) (VShape _dvo2 (LNest dvi2 lyt2)) = do
    (dvi, rv) <- vlNestProductS dvi1 dvi2
    lyt2'     <- repLayout rv lyt2
    let lyt  = LTuple [lyt1, lyt2']
    return $ VShape dvo1 (LNest dvi1 (LTuple [lyt1, (LNest dvi lyt)]))
nestProductL _ _ = $impossible

thetaJoinL :: L.JoinPredicate L.JoinExpr -> Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
thetaJoinL joinPred (VShape dvo1 (LNest dvi1 lyt1)) (VShape _ (LNest dvi2 lyt2)) = do
    (dvi, rv1, rv2) <- vlThetaJoinS joinPred dvi1 dvi2
    lyt1'           <- repLayout rv1 lyt1
    lyt2'           <- repLayout rv2 lyt2
    return $ VShape dvo1 (LNest dvi $ LTuple [lyt1', lyt2'])
thetaJoinL _ _ _ = $impossible

-- △^L :: [[a]] -> [[b]] -> [[(a, [(a, b)])]]

-- For the unlifted nestjoin, we could segment the left (outer) input
-- and then use the regular thetajoin implementation. This trick does
-- not work here, as the lifted thetajoin joins on the
-- descriptors. Therefore, we have to 'segment' **after** the join,
-- i.e. use the left input positions as descriptors
nestJoinL :: L.JoinPredicate L.JoinExpr -> Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
nestJoinL joinPred (VShape dvo1 (LNest dvi1 lyt1)) (VShape _ (LNest dvi2 lyt2)) = do
    (dv, rv2) <- vlNestJoinS joinPred dvi1 dvi2
    lyt2'     <- repLayout rv2 lyt2
    let lyt  = LTuple [lyt1, lyt2']
    return $ VShape dvo1 (LNest dvo1 (LTuple [lyt1, LNest dv lyt]))
nestJoinL _ _ _ = $impossible

semiJoinL :: L.JoinPredicate L.JoinExpr -> Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
semiJoinL joinPred (VShape dvo1 (LNest dvi1 lyt1)) (VShape _ (LNest dvi2 _)) = do
    (dv, fv) <- vlSemiJoinS joinPred dvi1 dvi2
    lyt1'    <- filterLayout fv lyt1
    return $ VShape dvo1 (LNest dv lyt1')
semiJoinL _ _ _ = $impossible

antiJoinL :: L.JoinPredicate L.JoinExpr -> Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
antiJoinL joinPred (VShape dvo1 (LNest dvi1 lyt1)) (VShape _ (LNest dvi2 _)) = do
    (dv, fv) <- vlAntiJoinS joinPred dvi1 dvi2
    lyt1'    <- filterLayout fv lyt1
    return $ VShape dvo1 (LNest dv lyt1')
antiJoinL _ _ _ = $impossible

nubL ::  Shape VLDVec -> Build VL (Shape VLDVec)
nubL (VShape d (LNest q lyt)) =  VShape d <$> (LNest <$> vlUniqueS q <*> pure lyt)
nubL _ = $impossible

numberL ::  Shape VLDVec -> Build VL (Shape VLDVec)
numberL (VShape d (LNest q lyt)) =
    VShape d <$> (LNest <$> vlNumberS q
                        <*> (pure $ LTuple [lyt, LCol]))
numberL _ = $impossible

initL ::  Shape VLDVec -> Build VL (Shape VLDVec)
initL (VShape qs (LNest q lyt)) = do
    is         <- vlAggrS AggrCount qs q
    (q', r, _) <- vlSelectPosS q (L.SBRelOp L.Lt) is
    lyt'       <- filterLayout r lyt
    return $ VShape qs (LNest q' lyt')
initL _ = $impossible

lastL ::  Shape VLDVec -> Build VL (Shape VLDVec)
lastL (VShape d (LNest qs lyt@(LNest _ _))) = do
    is          <- vlAggrS AggrCount d qs
    (qs', r, _) <- vlSelectPosS qs (L.SBRelOp L.Eq) is
    lyt'        <- filterLayout r lyt
    re          <- vlUnboxRename qs'
    VShape d <$> rekeyLayout re lyt'
lastL (VShape d (LNest qs lyt)) = do
    is          <- vlAggrS AggrCount d qs
    (qs', r, _) <- vlSelectPosS qs (L.SBRelOp L.Eq) is
    lyt'        <- filterLayout r lyt
    re          <- vlUnboxRename d
    VShape <$> vlAppKey re qs' <*> pure lyt'
lastL _ = $impossible

indexL ::  Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
indexL (VShape d (LNest qs (LNest qi lyti))) (VShape idxs LCol) = do
    idxs'          <- vlProject [BinApp (L.SBNumOp L.Add) (Column 1) (Constant $ L.IntV 1)] idxs
    (_, _, u)      <- vlSelectPosS qs (L.SBRelOp L.Eq) idxs'
    (qu, ri)       <- vlUnboxNested u qi
    lyti'          <- rekeyLayout ri lyti
    return $ VShape d (LNest qu lyti')
indexL (VShape d (LNest qs lyt)) (VShape idxs LCol) = do
    idxs'          <- vlProject [BinApp (L.SBNumOp L.Add) (Column 1) (Constant $ L.IntV 1)] idxs
    (qs', r, _)    <- vlSelectPosS qs (L.SBRelOp L.Eq) idxs'
    lyt'           <- filterLayout r lyt
    re             <- vlUnboxRename d
    VShape <$> vlAppKey re qs' <*> pure lyt'
indexL _ _ = $impossible

appendL ::  Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
appendL (VShape d lyt1) (VShape _ lyt2) = do
    VShape d <$> appendLayout lyt1 lyt2
appendL _ _ = $impossible

reverseL ::  Shape VLDVec -> Build VL (Shape VLDVec)
reverseL (VShape dvo (LNest dvi lyt)) = do
    (dv, sv) <- vlReverseS dvi
    lyt'     <- sortLayout sv lyt
    return (VShape dvo (LNest dv lyt'))
reverseL _ = $impossible

theL ::  Shape VLDVec -> Build VL (Shape VLDVec)
theL (VShape d (LNest q lyt)) = do
    (v, p2, _) <- vlSelectPos1S q (L.SBRelOp L.Eq) 1
    prop       <- vlUnboxRename d
    lyt'       <- filterLayout p2 lyt
    v'         <- vlAppKey prop v
    return $ VShape v' lyt'
theL _ = $impossible

tailL ::  Shape VLDVec -> Build VL (Shape VLDVec)
tailL (VShape d (LNest q lyt)) = do
    p              <- vlProject [Constant $ L.IntV 1] d
    (v, p2, _)     <- vlSelectPosS q (L.SBRelOp L.Gt) p
    lyt'           <- filterLayout p2 lyt
    return $ VShape d (LNest v lyt')
tailL _ = $impossible

sortL ::  Shape VLDVec -> Build VL (Shape VLDVec)
sortL (VShape dvo (LNest dvi (LTuple [xl, sl]))) = do
    let leftWidth  = columnsInLayout xl
        rightWidth = columnsInLayout sl

        sortExprs = map Column [leftWidth+1..leftWidth+rightWidth]

    -- Sort by all sorting columns from the right tuple component
    (sortedVec, sv) <- vlSortS sortExprs dvi

    -- After sorting, discard the sorting criteria columns
    resVec          <- vlProject (map Column [1..leftWidth]) sortedVec
    xl'             <- sortLayout sv xl
    return $ VShape dvo (LNest resVec xl')
sortL _ = $impossible

groupL ::  Shape VLDVec -> Build VL (Shape VLDVec)
groupL (VShape dvo (LNest dvi (LTuple [xl, gl]))) = do
    let leftWidth  = columnsInLayout xl
        rightWidth = columnsInLayout gl

        groupExprs = map Column [leftWidth+1..leftWidth+rightWidth]

    (dvo', dvi', rv) <- vlGroupS groupExprs dvi

    -- Discard the grouping columns in the inner vector
    dvi''            <- vlProject (map Column [1..leftWidth]) dvi'

    xl'              <- sortLayout rv xl
    return $ VShape dvo (LNest dvo' (LTuple [gl, LNest dvi'' xl']))
groupL _ = $impossible

concatL ::  Shape VLDVec -> Build VL (Shape VLDVec)
concatL (VShape d (LNest d' vs)) = do
    p   <- vlUnboxRename d'
    vs' <- rekeyLayout p vs
    return $ VShape d vs'
concatL _ = $impossible

lengthL ::  Shape VLDVec -> Build VL (Shape VLDVec)
lengthL (VShape q (LNest qi _)) = do
    ls  <- vlAggrS AggrCount q qi
    lsu <- vlUnboxScalar q ls
    return $ VShape lsu LCol
lengthL s = trace (show s) $ $impossible

outer ::  Shape VLDVec -> Build VL VLDVec
outer (SShape _ _)        = $impossible
outer (VShape q _)        = return q

aggrL :: (Expr -> AggrFun) -> Shape VLDVec -> Build VL (Shape VLDVec)
aggrL afun (VShape d (LNest q LCol)) = do
    qr <- vlAggrS (afun (Column 1)) d q
    qu <- vlUnboxScalar d qr
    return $ VShape qu LCol
aggrL _ _ = $impossible

distL ::  Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
distL (VShape dv1 lyt1) (VShape dvo2 (LNest dvi2 lyt2)) = do
    (dv, rv)        <- vlDistLift dv1 dvi2
    lyt1'           <- repLayout rv lyt1
    let lyt = LTuple [lyt1', lyt2]
    VShape dv' lytf <- tupElemL First $ VShape dv lyt
    return $ VShape dvo2 (LNest dv' lytf)
distL _e1 _e2 = $impossible

tupleL :: [Shape VLDVec] -> Build VL (Shape VLDVec)
tupleL shapes@(_ : _) = do
    (q, lyts) <- alignVectors shapes
    return $ VShape q (LTuple lyts)
tupleL _ = $impossible

tupElemL :: TupleIndex -> Shape VLDVec -> Build VL (Shape VLDVec)
tupElemL i (VShape q (LTuple lyts)) = do
    let (lyt', cols) = projectColumns i lyts
    proj <- vlProject (map Column cols) q
    return $ VShape proj lyt'
tupElemL i s = trace (show i ++ " " ++ show s) $impossible

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

projectColumns :: TupleIndex -> [Layout VLDVec] -> (Layout VLDVec, [DBCol])
projectColumns i lyts =
    let (prefixLyts, lyt : _) = splitAt (tupleIndex i - 1) lyts
        lytWidth              = columnsInLayout lyt
        prefixWidth           = sum $ map columnsInLayout prefixLyts
    in (lyt, [ c + prefixWidth | c <- [1..lytWidth] ])

singleton :: Shape VLDVec -> Build VL (Shape VLDVec)
singleton (VShape q lyt) = do
    VLDVec d <- vlSingletonDescr
    return $ VShape (VLDVec d) (LNest q lyt)
singleton (SShape q1 lyt) = return $ VShape q1 lyt

singletonL :: Shape VLDVec -> Build VL (Shape VLDVec)
singletonL (VShape q lyt) = do
    innerVec <- vlSegment q
    outerVec <- vlProject [] q
    return $ VShape outerVec (LNest innerVec lyt)
singletonL _ = $impossible

--------------------------------------------------------------------------------
-- Construction of base tables and literal tables

-- | Create a VL reference to a base table.
dbTable ::  String -> L.BaseTableSchema -> Build VL (Shape VLDVec)
dbTable n schema = do
    tab <- vlTableRef n schema
    -- Single-column tables are represented by a flat list and map to
    -- a flat one-column layout. Multi-column tables map to a list of
    -- tuples and the corresponding tuple layout.
    let lyt = case L.tableCols schema of
                  _ N.:| [] -> LCol
                  cs        -> LTuple $ map (const LCol) $ N.toList cs
    return $ VShape tab lyt

-- | Create a VL representation of a literal value.
mkLiteral ::  Type -> L.Val -> Build VL (Shape VLDVec)
-- Translate an outer list
mkLiteral t@(ListT _) (L.ListV es) = do
    ((tabTys, tabCols), lyt, _) <- toPlan (mkDescriptor [P.length es]) t 1 es
    let emptinessFlag = case es of
          []    -> L.PossiblyEmpty
          _ : _ -> L.NonEmpty
    litNode <- vlLit emptinessFlag (P.reverse tabTys) $ map P.reverse tabCols
    return $ VShape litNode lyt
-- Translate a non-list value, i.e. scalar or tuple
mkLiteral t e           = do
    -- There is only one element in the outermost vector
    ((tabTys, [tabCols]), layout, _) <- toPlan (mkDescriptor [1]) (ListT t) 1 [e]
    litNode <- vlLit L.NonEmpty (P.reverse tabTys) [(P.reverse tabCols)]
    return $ SShape litNode layout

type Table = ([Type], [[L.ScalarVal]])

-- | Add values to a vector. If necessary (i.e. inner lists are
-- encountered), create new inner vectors. 'toPlan' receives a
-- descriptor that has enough space for all elements of the list that
-- are currently encoded.

-- FIXME Check if inner list literals are nonempty and flag VL
-- literals appropriately.
toPlan ::  Table -> Type -> Int -> [L.Val] -> Build VL (Table, Layout VLDVec, Int)
toPlan (tabTys, tabCols) (ListT t) nextCol es =
    -- Inspect the element type of the list to be encoded
    case t of
        ListT _ -> do
            let vs = map listElems es
                -- Create a vector with one entry for each element of an inner list
                d  = mkDescriptor $ map P.length vs
            -- Add the inner list elements to the vector
            ((innerTabTys, innerTabCols), lyt, _) <- toPlan d t 1 (P.concat vs)
            n <- vlLit L.PossiblyEmpty (P.reverse innerTabTys) (map P.reverse innerTabCols)
            return ((tabTys, tabCols), LNest n lyt, nextCol)

        TupleT elemTys -> do
            -- We add tuple elements column-wise. If the list to be
            -- encoded is empty, create an empty list for each column.
            let colsVals = case es of
                               [] -> map (const []) elemTys
                               _  -> List.transpose $ map tupleElems es
            mkTupleTable (tabTys, tabCols) nextCol [] colsVals elemTys

        _ -> let (hd, vs) = mkColumn t es
             in return ((hd:tabTys, zipWith (:) vs tabCols), LCol, nextCol + 1)

toPlan (tabTys, tabCols) t c v =
    let (hd, v') = mkColumn t v
    in return $ ((hd:tabTys, zipWith (:) v' tabCols), LCol, c + 1)

-- | Construct the literal table for a list of tuples.
mkTupleTable :: Table                         -- ^ The literal table so far.
   -> Int                                     -- ^ The next available column offset
   -> [Layout VLDVec]                         -- ^ The layouts of the tuple elements constructed so far
   -> [[L.Val]]                               -- ^ Values for the tuple elements
   -> [Type]                                  -- ^ Types for the tuple elements
   -> Build VL (Table, Layout VLDVec, Int)
mkTupleTable tab nextCol lyts (colVals : colsVals) (t : ts) = do
    (tab', lyt, nextCol') <- toPlan tab (ListT t) nextCol colVals
    mkTupleTable tab' nextCol' (lyt : lyts) colsVals ts
mkTupleTable tab nextCol lyts []                   []       = do
    return $ (tab, LTuple $ P.reverse lyts, nextCol)
mkTupleTable _   _       _    _                    _        = $impossible

literal :: Type -> L.ScalarVal -> Build VL VLDVec
literal t v = vlLit L.NonEmpty [t] [[L.IntV 1, L.IntV 1, v]]

listElems :: L.Val -> [L.Val]
listElems (L.ListV es) = es
listElems _            = $impossible

tupleElems :: L.Val -> [L.Val]
tupleElems (L.TupleV es) = es
tupleElems _             = $impossible

mkColumn :: Type -> [L.Val] -> (Type, [L.ScalarVal])
mkColumn t vs = (t, [pVal v | v <- vs])

mkDescriptor :: [Int] -> Table
mkDescriptor lengths =
    let header = []
        body   = [ [L.IntV $ fromInteger p, L.IntV $ fromInteger d]
                 | d <- P.concat [ replicate l p | p <- [1..] | l <- lengths ]
                 | p <- [1..]
                 ]
    in (header, body)

--------------------------------------------------------------------------------
-- Helper functions for zipping/tuple construction

-- | Simply align a list of shapes and collect their layouts.
alignVectors :: [Shape VLDVec] -> Build VL (VLDVec, [Layout VLDVec])
alignVectors (VShape q1 lyt1 : [])     = return (q1, [lyt1])
alignVectors (VShape q1 lyt1 : shapes) = do
    (q, lyts) <- alignVectors shapes
    qz' <- vlAlign q1 q
    return (qz', lyt1 : lyts)
alignVectors _ = $impossible

-- | Align a list of shapes and nest vectors if necessary. This helper
-- function covers tuple construction in the unlifted case.
boxVectors :: [Shape VLDVec] -> Build VL (VLDVec, [Layout VLDVec])
boxVectors (SShape q1 lyt1 : [])     = return (q1, [lyt1])
boxVectors (VShape q1 lyt1 : [])     = do
    qo <- vlSingletonDescr
    qi <- vlUnsegment q1
    return (qo, [LNest qi lyt1])
boxVectors (SShape q1 lyt1 : shapes) = do
    (q, lyts) <- boxVectors shapes
    qz'       <- vlAlign q1 q
    return (qz', lyt1 : lyts)
boxVectors (VShape q1 lyt1 : shapes) = do
    (q, lyts) <- boxVectors shapes
    q1'       <- vlUnsegment q1
    return (q, LNest q1' lyt1 : lyts)
boxVectors s = error $ show s

--------------------------------------------------------------------------------
-- Compile-time operations that implement higher-lifted primitives.

-- | Remove the 'n' outer layers of nesting from a nested list
-- (Prins/Palmer: 'extract').
forget :: Nat -> Shape VLDVec -> Shape VLDVec
forget Zero _                               = $impossible
forget (Succ Zero) (VShape _ (LNest q lyt)) = VShape q lyt
forget (Succ n)    (VShape _ lyt)           = extractInnerVec n lyt
forget _           _                        = $impossible

extractInnerVec :: Nat -> Layout VLDVec -> Shape VLDVec
extractInnerVec (Succ Zero) (LNest _ (LNest q lyt)) = VShape q lyt
extractInnerVec (Succ n)    (LNest _ lyt)           = extractInnerVec n lyt
extractInnerVec n           l                       = trace (show n ++ " " ++ show l) $impossible

-- | Prepend the 'n' outer layers of nesting from the first input to
-- the second input (Prins/Palmer: 'insert').
imprint :: Nat -> Shape VLDVec -> Shape VLDVec -> Shape VLDVec
imprint (Succ Zero) (VShape d _) (VShape vi lyti) =
    VShape d (LNest vi lyti)
imprint (Succ n) (VShape d lyt) (VShape vi lyti)  =
    VShape d (implantInnerVec n lyt vi lyti)
imprint _          _                   _          =
    $impossible

implantInnerVec :: Nat -> Layout VLDVec -> VLDVec -> Layout VLDVec -> Layout VLDVec
implantInnerVec (Succ Zero) (LNest d _)   vi lyti   =
    LNest d $ LNest vi lyti
implantInnerVec (Succ n)      (LNest d lyt) vi lyti =
    LNest d $ implantInnerVec n lyt vi lyti
implantInnerVec _          _            _  _        =
    $impossible

--------------------------------------------------------------------------------
-- Vectorization Helper Functions

-- | Take a shape apart by extracting the vector, the layout and the
-- shape constructor itself.
unwrapShape :: Shape VLDVec -> (VLDVec -> Layout VLDVec -> Shape VLDVec, VLDVec, Layout VLDVec)
unwrapShape (VShape q lyt) = (VShape, q, lyt)
unwrapShape (SShape q lyt) = (SShape, q, lyt)

appLayout :: v
          -> (v -> VLDVec -> Build VL (VLDVec, v))
          -> Layout VLDVec
          -> Build VL (Layout VLDVec)
appLayout _ _ LCol = return LCol
appLayout v appVec (LNest d l) = do
    (d', v') <- appVec v d
    l'       <- appLayout v' appVec l
    return $ LNest d' l'
appLayout v appVec (LTuple ls) =
    LTuple <$> mapM (appLayout v appVec) ls

filterLayout :: VLFVec -> Layout VLDVec -> Build VL (Layout VLDVec)
filterLayout v l = appLayout v vlAppFilter l

repLayout :: VLRVec -> Layout VLDVec -> Build VL (Layout VLDVec)
repLayout v l = appLayout v vlAppRep l

sortLayout :: VLSVec -> Layout VLDVec -> Build VL (Layout VLDVec)
sortLayout v l = appLayout v vlAppSort l

rekeyLayout :: VLKVec -> Layout VLDVec -> Build VL (Layout VLDVec)
rekeyLayout _ LCol          = return LCol
rekeyLayout r (LNest q lyt) = LNest <$> vlAppKey r q <*> pure lyt
rekeyLayout r (LTuple lyts) = LTuple <$> mapM (rekeyLayout r) lyts

-- | Traverse a layout and append all nested vectors that are
-- encountered.
appendLayout :: Layout VLDVec -> Layout VLDVec -> Build VL (Layout VLDVec)
appendLayout LCol LCol = return LCol
-- Append two nested vectors
appendLayout (LNest dv1 lyt1) (LNest dv2 lyt2) = do
    -- Append the current vectors
    (dv12, kv1, kv2) <- vlAppendS dv1 dv2
    -- Propagate position changes to descriptors of any inner vectors
    lyt1'       <- rekeyLayout kv1 lyt1
    lyt2'       <- rekeyLayout kv2 lyt2
    -- Append the layouts, i.e. actually append all inner vectors
    lyt'        <- appendLayout lyt1' lyt2'
    return $ LNest dv12 lyt'
appendLayout (LTuple lyts1) (LTuple lyts2) =
    LTuple <$> (sequence $ zipWith appendLayout lyts1 lyts2)
appendLayout _ _ = $impossible
