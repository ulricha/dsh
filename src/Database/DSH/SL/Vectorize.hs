{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TemplateHaskell  #-}

-- | Vectorising constructor functions that implement FKL primitives
-- using SL operators.
module Database.DSH.SL.Vectorize where

import           Control.Applicative
import           Control.Monad
import qualified Data.List                      as List
import qualified Data.List.NonEmpty             as N
import qualified Data.Sequence                  as S
import           Prelude                        hiding (reverse, zip)

import           Database.Algebra.Dag.Build

import           Database.DSH.Common.Impossible
import qualified Database.DSH.Common.Lang       as L
import           Database.DSH.Common.Nat
import           Database.DSH.Common.QueryPlan
import           Database.DSH.Common.Type
import           Database.DSH.Common.Vector
import           Database.DSH.Common.VectorLang
import           Database.DSH.SL.Lang           (SL ())
import           Database.DSH.SL.Primitives

{-# ANN module "HLint: ignore Reduce duplication" #-}

--------------------------------------------------------------------------------
-- Construction of not-lifted primitives

binOp :: L.ScalarBinOp -> Shape SLDVec -> Shape SLDVec -> Build SL (Shape SLDVec)
binOp o (SShape dv1 _) (SShape dv2 _) = do
    (dv, _, _) <- vlCartProduct dv1 dv2
    dv'        <- vlProject [BinApp o (Column 1) (Column 2)] dv
    return $ SShape dv' LCol
binOp _ _ _ = $impossible

zip ::  Shape SLDVec -> Shape SLDVec -> Build SL (Shape SLDVec)
zip (VShape dv1 lyt1) (VShape dv2 lyt2) = do
    (dv, fv1, fv2) <- vlZip dv1 dv2
    lyt1'          <- rekeyOuter fv1 lyt1
    lyt2'          <- rekeyOuter fv2 lyt2
    return $ VShape dv $ LTuple [lyt1', lyt2']
zip _ _ = $impossible

cartProduct :: Shape SLDVec -> Shape SLDVec -> Build SL (Shape SLDVec)
cartProduct (VShape dv1 lyt1) (VShape dv2 lyt2) = do
    (dv, rv1, rv2) <- vlCartProduct dv1 dv2
    lyt1'          <- repLayout rv1 lyt1
    lyt2'          <- repLayout rv2 lyt2
    return $ VShape dv $ LTuple [lyt1', lyt2']
cartProduct _ _ = $impossible

thetaJoin :: L.JoinPredicate L.ScalarExpr -> Shape SLDVec -> Shape SLDVec -> Build SL (Shape SLDVec)
thetaJoin joinPred (VShape dv1 lyt1) (VShape dv2 lyt2) = do
    (dv, rv1, rv2) <- vlThetaJoin joinPred dv1 dv2
    lyt1'          <- repLayout rv1 lyt1
    lyt2'          <- repLayout rv2 lyt2
    return $ VShape dv $ LTuple [lyt1', lyt2']
thetaJoin _ _ _ = $impossible

nestJoin :: L.JoinPredicate L.ScalarExpr -> Shape SLDVec -> Shape SLDVec -> Build SL (Shape SLDVec)
nestJoin joinPred (VShape dv1 lyt1) (VShape dv2 lyt2) = do
    (dv, rv1, rv2) <- vlNestJoin joinPred dv1 dv2
    lyt1'          <- repLayout rv1 lyt1
    lyt2'          <- repLayout rv2 lyt2
    return $ VShape dv1 (LTuple [lyt1, LNest dv (LTuple [lyt1', lyt2'])])
nestJoin _ _ _ = $impossible

groupJoin :: L.JoinPredicate L.ScalarExpr
          -> L.NE AggrFun
          -> Shape SLDVec
          -> Shape SLDVec -> Build SL (Shape SLDVec)
groupJoin joinPred afuns (VShape dv1 lyt1) (VShape dv2 _) = do
    dv <- vlGroupJoin joinPred afuns dv1 dv2
    return $ VShape dv (LTuple $ lyt1 : map (const LCol) (N.toList $ L.getNE afuns))
groupJoin _ _ _ _ = $impossible

semiJoin :: L.JoinPredicate L.ScalarExpr -> Shape SLDVec -> Shape SLDVec -> Build SL (Shape SLDVec)
semiJoin joinPred (VShape dv1 lyt1) (VShape dv2 _) = do
    (dv, fv) <- vlSemiJoin joinPred dv1 dv2
    lyt1'    <- filterLayout fv lyt1
    return $ VShape dv lyt1'
semiJoin _ _ _ = $impossible

antiJoin :: L.JoinPredicate L.ScalarExpr -> Shape SLDVec -> Shape SLDVec -> Build SL (Shape SLDVec)
antiJoin joinPred (VShape dv1 lyt1) (VShape dv2 _) = do
    (dv, fv) <- vlAntiJoin joinPred dv1 dv2
    lyt1'    <- filterLayout fv lyt1
    return $ VShape dv lyt1'
antiJoin _ _ _ = $impossible

nub ::  Shape SLDVec -> Build SL (Shape SLDVec)
nub (VShape dv lyt) = VShape <$> vlUnique dv <*> pure lyt
nub _ = $impossible

number ::  Shape SLDVec -> Build SL (Shape SLDVec)
number (VShape q lyt) =
    VShape <$> vlNumber q <*> pure (LTuple [lyt, LCol])
number _ = $impossible

append ::  Shape SLDVec -> Shape SLDVec -> Build SL (Shape SLDVec)
append (VShape dv1 lyt1) (VShape dv2 lyt2) = do
    -- Append the current vectors
    (dv12, kv1, kv2) <- vlAppend dv1 dv2
    -- Propagate position changes to descriptors of any inner vectors
    lyt1'       <- rekeyOuter kv1 lyt1
    lyt2'       <- rekeyOuter kv2 lyt2
    -- Append the layouts, i.e. actually append all inner vectors
    lyt'        <- appendLayout lyt1' lyt2'
    return $ VShape dv12 lyt'
append _ _ = $impossible

reverse ::  Shape SLDVec -> Build SL (Shape SLDVec)
reverse (VShape dv lyt) = do
    (dv', sv) <- vlReverse dv
    lyt'      <- sortLayout sv lyt
    return (VShape dv' lyt')
reverse _ = $impossible

sort :: Shape SLDVec -> Build SL (Shape SLDVec)
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
group ::  Shape SLDVec -> Build SL (Shape SLDVec)
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

length_ ::  Shape SLDVec -> Build SL (Shape SLDVec)
length_ (VShape q _) = do
    v  <- vlAggr AggrCount q
    return $ SShape v LCol
length_ _ = $impossible

restrict ::  Shape SLDVec -> Build SL (Shape SLDVec)
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
restrict _ = $impossible

combine ::  Shape SLDVec -> Shape SLDVec -> Shape SLDVec -> Build SL (Shape SLDVec)
combine (VShape dvb LCol) (VShape dv1 lyt1) (VShape dv2 lyt2) = do
    (dv, kv1, kv2) <- vlCombine dvb dv1 dv2
    lyt1'          <- rekeyOuter kv1 lyt1
    lyt2'          <- rekeyOuter kv2 lyt2
    lyt'           <- appendLayout lyt1' lyt2'
    return $ VShape dv lyt'
combine _ _ _ = $impossible

-- | Distribute a single value in vector 'dv2' over an arbitrary
-- (inner) vector.
distSingleton :: SLDVec                  -- ^ The singleton outer vector
              -> Layout SLDVec           -- ^ The outer vector's layout
              -> SLDVec                  -- ^ The inner vector distributed over
              -> Build SL (Shape SLDVec)
distSingleton dv1 lyt1 dv2 = do
    let leftWidth  = columnsInLayout lyt1
        proj       = map Column [1..leftWidth]

    (dv, rv) <- dv1 `vlReplicateScalar` dv2
    dv'      <- vlProject proj dv

    lyt'     <- repLayout rv lyt1
    return $ VShape dv' lyt'

dist ::  Shape SLDVec -> Shape SLDVec -> Build SL (Shape SLDVec)
dist (SShape dv lyt) (VShape dv1 _)    = distSingleton dv lyt dv1
dist (VShape dv lyt) (VShape dvo _) = do
    (prodVec, rv)    <- vlReplicateVector dvo dv

    -- The outer vector does not have columns, it only describes the
    -- shape.
    outerVec         <- vlProject [] dvo

    -- Replicate any inner vectors
    lyt'             <- repLayout rv lyt

    return $ VShape outerVec (LNest prodVec lyt')
dist _ _ = $impossible

only :: Shape SLDVec -> Build SL (Shape SLDVec)
only (VShape _ (LNest qi lyti)) = VShape <$> vlUnsegment qi <*> pure lyti
only (VShape q lyt)             = SShape <$> vlUnsegment q <*> pure lyt
only _                          = $impossible

aggr :: (Expr -> AggrFun) -> Shape SLDVec -> Build SL (Shape SLDVec)
aggr afun (VShape q LCol) =
    SShape <$> vlAggr (afun (Column 1)) q <*> pure LCol
aggr _ _ = $impossible

ifList ::  Shape SLDVec -> Shape SLDVec -> Shape SLDVec -> Build SL (Shape SLDVec)
ifList (SShape qb lytb) (VShape q1 lyt1) (VShape q2 lyt2) = do
    let leftWidth = columnsInLayout lyt1
        predicate = Column $ leftWidth + 1

    VShape trueSelVec _  <- distSingleton qb lytb q1
    (trueVec, truefv)    <- vlSelect predicate
                            =<< vlAlign q1 trueSelVec
    trueVec'             <- vlProject (map Column [1..leftWidth]) trueVec

    let predicate' = UnApp (L.SUBoolOp L.Not) predicate

    VShape falseSelVec _ <- distSingleton qb lytb q2
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

tuple :: [Shape SLDVec] -> Build SL (Shape SLDVec)
tuple shapes@(_ : _) = do
    (q, lyts) <- boxVectors shapes
    return $ SShape q (LTuple lyts)
tuple _ = $impossible

tupElem :: TupleIndex -> Shape SLDVec -> Build SL (Shape SLDVec)
tupElem i (SShape q (LTuple lyts)) =
    case lyts !! (tupleIndex i - 1) of
        LNest qi lyt -> VShape <$> vlUnsegment qi <*> pure lyt
        _            -> do
            let (lyt', cols) = projectColumns i lyts
            proj <- vlProject (map Column cols) q
            return $ SShape proj lyt'
tupElem _ _ = $impossible

concat :: Shape SLDVec -> Build SL (Shape SLDVec)
concat (VShape _ (LNest q lyt)) = VShape <$> vlUnsegment q <*> pure lyt
concat _e                       = $impossible

--------------------------------------------------------------------------------
-- Construction of lifted primitives

onlyL :: Shape SLDVec -> Build SL (Shape SLDVec)
onlyL (VShape dvo (LNest dvi lyt)) = do
    (dv, kv) <- vlUnboxSng dvo dvi
    lyt'     <- rekeyOuter kv lyt
    return $ VShape dv lyt'
onlyL _                           = $impossible

binOpL :: L.ScalarBinOp -> Shape SLDVec -> Shape SLDVec -> Build SL (Shape SLDVec)
binOpL o (VShape dv1 _) (VShape dv2 _) = do
    dv <- vlProject [BinApp o (Column 1) (Column 2)] =<< vlAlign dv1 dv2
    return $ VShape dv LCol
binOpL _ _ _ = $impossible

restrictL :: Shape SLDVec -> Build SL (Shape SLDVec)
restrictL (VShape qo (LNest qi lyt)) = do
    VShape qi' lyt' <- restrict (VShape qi lyt)
    return $ VShape qo (LNest qi' lyt')
restrictL _ = $impossible

combineL :: Shape SLDVec -> Shape SLDVec -> Shape SLDVec -> Build SL (Shape SLDVec)
combineL (VShape qo (LNest qb LCol))
         (VShape _ (LNest qi1 lyt1))
         (VShape _ (LNest qi2 lyt2)) = do
    VShape qi' lyt' <- combine (VShape qb LCol) (VShape qi1 lyt1) (VShape qi2 lyt2)
    return $ VShape qo (LNest qi' lyt')
combineL _ _ _ = $impossible

zipL ::  Shape SLDVec -> Shape SLDVec -> Build SL (Shape SLDVec)
zipL (VShape d1 (LNest q1 lyt1)) (VShape _ (LNest q2 lyt2)) = do
    (q', r1, r2) <- vlZip q1 q2
    lyt1'        <- rekeyLayout r1 lyt1
    lyt2'        <- rekeyLayout r2 lyt2
    return $ VShape d1 (LNest q' $ LTuple [lyt1', lyt2'])
zipL _ _ = $impossible

cartProductL :: Shape SLDVec -> Shape SLDVec -> Build SL (Shape SLDVec)
cartProductL (VShape dvo1 (LNest dvi1 lyt1)) (VShape _ (LNest dvi2 lyt2)) = do
    (dv, rv1, rv2) <- vlCartProduct dvi1 dvi2
    lyt1'        <- repLayout rv1 lyt1
    lyt2'        <- repLayout rv2 lyt2
    return $ VShape dvo1 (LNest dv $ LTuple [lyt1', lyt2'])
cartProductL _ _ = $impossible

thetaJoinL :: L.JoinPredicate L.ScalarExpr -> Shape SLDVec -> Shape SLDVec -> Build SL (Shape SLDVec)
thetaJoinL joinPred (VShape dvo1 (LNest dvi1 lyt1)) (VShape _ (LNest dvi2 lyt2)) = do
    (dvi, rv1, rv2) <- vlThetaJoin joinPred dvi1 dvi2
    lyt1'           <- repLayout rv1 lyt1
    lyt2'           <- repLayout rv2 lyt2
    return $ VShape dvo1 (LNest dvi $ LTuple [lyt1', lyt2'])
thetaJoinL _ _ _ = $impossible

-- △^L :: [[a]] -> [[b]] -> [[(a, [(a, b)])]]
nestJoinL :: L.JoinPredicate L.ScalarExpr -> Shape SLDVec -> Shape SLDVec -> Build SL (Shape SLDVec)
nestJoinL joinPred (VShape dvo1 (LNest dvi1 lyt1)) (VShape _ (LNest dvi2 lyt2)) = do
    (dv, rv1, rv2) <- vlNestJoin joinPred dvi1 dvi2
    lyt1'          <- repLayout rv1 lyt1
    lyt2'          <- repLayout rv2 lyt2
    let lyt  = LTuple [lyt1', lyt2']
    return $ VShape dvo1 (LNest dvi1 (LTuple [lyt1, LNest dv lyt]))
nestJoinL _ _ _ = $impossible

groupJoinL :: L.JoinPredicate L.ScalarExpr
           -> L.NE AggrFun
           -> Shape SLDVec
           -> Shape SLDVec
           -> Build SL (Shape SLDVec)
groupJoinL joinPred afuns (VShape dvo1 (LNest dvi1 lyt1)) (VShape _ (LNest dvi2 _)) = do
    dv <- vlGroupJoin joinPred afuns dvi1 dvi2
    return $ VShape dvo1 (LNest dv (LTuple (lyt1 : map (const LCol) (N.toList $ L.getNE afuns))))
groupJoinL _ _ _ _ = $impossible

semiJoinL :: L.JoinPredicate L.ScalarExpr -> Shape SLDVec -> Shape SLDVec -> Build SL (Shape SLDVec)
semiJoinL joinPred (VShape dvo1 (LNest dvi1 lyt1)) (VShape _ (LNest dvi2 _)) = do
    (dv, fv) <- vlSemiJoin joinPred dvi1 dvi2
    lyt1'    <- filterLayout fv lyt1
    return $ VShape dvo1 (LNest dv lyt1')
semiJoinL _ _ _ = $impossible

antiJoinL :: L.JoinPredicate L.ScalarExpr -> Shape SLDVec -> Shape SLDVec -> Build SL (Shape SLDVec)
antiJoinL joinPred (VShape dvo1 (LNest dvi1 lyt1)) (VShape _ (LNest dvi2 _)) = do
    (dv, fv) <- vlAntiJoin joinPred dvi1 dvi2
    lyt1'    <- filterLayout fv lyt1
    return $ VShape dvo1 (LNest dv lyt1')
antiJoinL _ _ _ = $impossible

nubL ::  Shape SLDVec -> Build SL (Shape SLDVec)
nubL (VShape d (LNest q lyt)) =  VShape d <$> (LNest <$> vlUnique q <*> pure lyt)
nubL _ = $impossible

numberL ::  Shape SLDVec -> Build SL (Shape SLDVec)
numberL (VShape d (LNest q lyt)) =
    VShape d <$> (LNest <$> vlNumber q
                        <*> pure (LTuple [lyt, LCol]))
numberL _ = $impossible

appendL ::  Shape SLDVec -> Shape SLDVec -> Build SL (Shape SLDVec)
appendL (VShape d lyt1) (VShape _ lyt2) = VShape d <$> appendLayout lyt1 lyt2
appendL _ _ = $impossible

reverseL ::  Shape SLDVec -> Build SL (Shape SLDVec)
reverseL (VShape dvo (LNest dvi lyt)) = do
    (dv, sv) <- vlReverse dvi
    lyt'     <- sortLayout sv lyt
    return (VShape dvo (LNest dv lyt'))
reverseL _ = $impossible

sortL ::  Shape SLDVec -> Build SL (Shape SLDVec)
sortL (VShape dvo (LNest dvi (LTuple [xl, sl]))) = do
    let leftWidth  = columnsInLayout xl
        rightWidth = columnsInLayout sl

        sortExprs = map Column [leftWidth+1..leftWidth+rightWidth]

    -- Sort by all sorting columns from the right tuple component
    (sortedVec, sv) <- vlSort sortExprs dvi

    -- After sorting, discard the sorting criteria columns
    resVec          <- vlProject (map Column [1..leftWidth]) sortedVec
    xl'             <- sortLayout sv xl
    return $ VShape dvo (LNest resVec xl')
sortL _ = $impossible

groupL ::  Shape SLDVec -> Build SL (Shape SLDVec)
groupL (VShape dvo (LNest dvi (LTuple [xl, gl]))) = do
    let leftWidth  = columnsInLayout xl
        rightWidth = columnsInLayout gl

        groupExprs = map Column [leftWidth+1..leftWidth+rightWidth]

    (dvo', dvi', rv) <- vlGroup groupExprs dvi

    -- Discard the grouping columns in the inner vector
    dvi''            <- vlProject (map Column [1..leftWidth]) dvi'

    xl'              <- sortLayout rv xl
    return $ VShape dvo (LNest dvo' (LTuple [gl, LNest dvi'' xl']))
groupL _ = $impossible

concatL ::  Shape SLDVec -> Build SL (Shape SLDVec)
concatL (VShape d (LNest d' vs)) = do
    p   <- vlUnboxKey d'
    vs' <- rekeyOuter p vs
    return $ VShape d vs'
concatL _ = $impossible

lengthL ::  Shape SLDVec -> Build SL (Shape SLDVec)
lengthL (VShape q (LNest qi _)) = do
    ls  <- vlAggrSeg AggrCount q qi
    lsu <- fst <$> vlUnboxSng q ls
    return $ VShape lsu LCol
lengthL _ = $impossible

outer ::  Shape SLDVec -> Build SL SLDVec
outer (SShape _ _)        = $impossible
outer (VShape q _)        = return q

aggrL :: (Expr -> AggrFun) -> Shape SLDVec -> Build SL (Shape SLDVec)
aggrL afun (VShape d (LNest q LCol)) = do
    qr <- vlAggrSeg (afun (Column 1)) d q
    qu <- fst <$> vlUnboxSng d qr
    return $ VShape qu LCol
aggrL _ _ = $impossible

distL ::  Shape SLDVec -> Shape SLDVec -> Build SL (Shape SLDVec)
distL (VShape dv1 lyt1) (VShape dvo2 (LNest dvi2 lyt2)) = do
    (dv, rv)        <- vlReplicateNest dv1 dvi2
    lyt1'           <- repLayout rv lyt1
    let lyt = LTuple [lyt1', lyt2]
    VShape dv' lytf <- tupElemL First $ VShape dv lyt
    return $ VShape dvo2 (LNest dv' lytf)
distL _e1 _e2 = $impossible

tupleL :: [Shape SLDVec] -> Build SL (Shape SLDVec)
tupleL shapes@(_ : _) = do
    (q, lyts) <- alignVectors shapes
    return $ VShape q (LTuple lyts)
tupleL _ = $impossible

tupElemL :: TupleIndex -> Shape SLDVec -> Build SL (Shape SLDVec)
tupElemL i (VShape q (LTuple lyts)) = do
    let (lyt', cols) = projectColumns i lyts
    proj <- vlProject (map Column cols) q
    return $ VShape proj lyt'
tupElemL _ _ = $impossible

projectColumns :: TupleIndex -> [Layout SLDVec] -> (Layout SLDVec, [DBCol])
projectColumns i lyts =
    let (prefixLyts, lyt : _) = splitAt (tupleIndex i - 1) lyts
        lytWidth              = columnsInLayout lyt
        prefixWidth           = sum $ map columnsInLayout prefixLyts
    in (lyt, [ c + prefixWidth | c <- [1..lytWidth] ])

singleton :: Shape SLDVec -> Build SL (Shape SLDVec)
singleton (VShape q lyt) = do
    (dvo, dvi) <- vlNest q
    return $ VShape dvo (LNest dvi lyt)
singleton (SShape q1 lyt) = return $ VShape q1 lyt

singletonL :: Shape SLDVec -> Build SL (Shape SLDVec)
singletonL (VShape q lyt) = do
    dvo <- vlProject [] q
    dvi <- vlSegment q
    return $ VShape dvo (LNest dvi lyt)
singletonL _ = $impossible

--------------------------------------------------------------------------------
-- Construction of base tables and literal tables

-- | Create a SL reference to a base table.
dbTable :: String -> L.BaseTableSchema -> Build SL (Shape SLDVec)
dbTable n schema = do
    tab <- vlTableRef n schema
    -- Single-column tables are represented by a flat list and map to
    -- a flat one-column layout. Multi-column tables map to a list of
    -- tuples and the corresponding tuple layout.
    let lyt = case L.tableCols schema of
                  _ N.:| [] -> LCol
                  cs        -> LTuple $ map (const LCol) $ N.toList cs
    return $ VShape tab lyt

--------------------------------------------------------------------------------
-- Shredding literal values

scalarVal :: L.Val -> L.ScalarVal
scalarVal (L.ScalarV v) = v
scalarVal _             = $impossible

fromList :: L.Val -> [L.Val]
fromList (L.ListV es) = es
fromList _            = $impossible

fromTuple :: L.Val -> [L.Val]
fromTuple (L.TupleV es) = es
fromTuple _             = $impossible

-- | Turn list elements into vector columns and encode inner lists in separate
-- vectors.
--
-- 'toColumns' receives the element type of the list and all element values of
-- the list.
toColumns :: Type -> [L.Val] -> Build SL ([ScalarType], [Column], Layout SLDVec)
toColumns (ListT t) ls    = do
    (v, lyt) <- toVector t ls
    return ([], [], LNest v lyt)
toColumns (TupleT tys) ts = do
    let tupleComponents = if null ts
                          then map (const []) tys
                          else List.transpose $ map fromTuple ts
    (colTys, cols, lyts) <- unzip3 <$> zipWithM toColumns tys tupleComponents
    return (List.concat colTys, List.concat cols, LTuple lyts)
toColumns (ScalarT t) vs  = return ([t], [S.fromList $ map scalarVal vs], LCol)

-- | Divide columns into segments according to the length of the original inner
-- lists.
chopSegments :: [Int] -> [Column] -> [Segment]
chopSegments (l:ls) cols =
    let (seg, cols') = unzip $ map (S.splitAt l) cols
    in Seg seg l : chopSegments ls cols'
chopSegments []     _    = []

-- | Encode all inner list values for a list type constructor in a vector.
--
-- 'toVector' receives the element type of the inner lists and all inner list
-- values.
toVector :: Type -> [L.Val] -> Build SL (SLDVec, Layout SLDVec)
toVector t ls = do
    -- Concatenate the elements of all inner lists
    let innerLists = map fromList ls
        allElems   = List.concat innerLists
        innerLens  = map length innerLists
    (tys, cols, lyt) <- toColumns t allElems
    let segs = chopSegments innerLens cols
    litNode <- vlLit (tys, SegFrame $ length allElems, Segs segs)
    return (litNode, lyt)

-- | Shred a literal value into flat vectors.
shredLiteral ::  Type -> L.Val -> Build SL (Shape SLDVec)
shredLiteral (ScalarT t) v = do
    (_, cols, _) <- toColumns (ScalarT t) [v]
    litNode <- vlLit ([t], SegFrame 1, UnitSeg cols)
    return $ SShape litNode LCol
shredLiteral (TupleT t)  v  = do
    (tys, cols, lyt) <- toColumns (TupleT t) [v]
    litNode <- vlLit (tys, SegFrame 1, UnitSeg cols)
    return $ SShape litNode lyt
shredLiteral (ListT t) (L.ListV es) = do
    (tys, cols, lyt) <- toColumns t es
    litNode <- vlLit (tys, SegFrame $ length es, UnitSeg cols)
    return $ VShape litNode lyt
shredLiteral _ _ = $impossible

--------------------------------------------------------------------------------
-- Helper functions for zipping/tuple construction

-- | Simply align a list of shapes and collect their layouts.
alignVectors :: [Shape SLDVec] -> Build SL (SLDVec, [Layout SLDVec])
alignVectors [VShape q1 lyt1]          = return (q1, [lyt1])
alignVectors (VShape q1 lyt1 : shapes) = do
    (q, lyts) <- alignVectors shapes
    qz' <- vlAlign q1 q
    return (qz', lyt1 : lyts)
alignVectors _ = $impossible

-- | Align a list of shapes and nest vectors if necessary. This helper
-- function covers tuple construction in the unlifted case.
boxVectors :: [Shape SLDVec] -> Build SL (SLDVec, [Layout SLDVec])
boxVectors [SShape q1 lyt1]           = return (q1, [lyt1])
boxVectors [VShape q1 lyt1]           = do
    (dvo, dvi) <- vlNest q1
    return (dvo, [LNest dvi lyt1])
boxVectors (SShape dv1 lyt1 : shapes) = do
    (dv, lyts)      <- boxVectors shapes
    (dv', rv1, rv2) <- vlCartProduct dv1 dv
    lyt1'           <- repLayout rv1 lyt1
    lyts'           <- mapM (repLayout rv2) lyts
    return (dv', lyt1' : lyts')
boxVectors (VShape dv1 lyt1 : shapes) = do
    (dv, lyts)      <- boxVectors shapes
    (dvo, dvi)      <- vlNest dv1
    (dv', rv1, rv2) <- vlCartProduct dvo dv
    lyt1'           <- repLayout rv1 (LNest dvi lyt1)
    lyts'           <- mapM (repLayout rv2) lyts
    return (dv', lyt1' : lyts')
boxVectors s = error $ show s

--------------------------------------------------------------------------------
-- Compile-time operations that implement higher-lifted primitives.

-- | Remove the 'n' outer layers of nesting from a nested list
-- (Prins/Palmer: 'extract').
forget :: Nat -> Shape SLDVec -> Shape SLDVec
forget Zero _                               = $impossible
forget (Succ Zero) (VShape _ (LNest q lyt)) = VShape q lyt
forget (Succ n)    (VShape _ lyt)           = extractInnerVec n lyt
forget _           _                        = $impossible

extractInnerVec :: Nat -> Layout SLDVec -> Shape SLDVec
extractInnerVec (Succ Zero) (LNest _ (LNest q lyt)) = VShape q lyt
extractInnerVec (Succ n)    (LNest _ lyt)           = extractInnerVec n lyt
extractInnerVec _           _                       = $impossible

-- | Prepend the 'n' outer layers of nesting from the first input to
-- the second input (Prins/Palmer: 'insert').
imprint :: Nat -> Shape SLDVec -> Shape SLDVec -> Shape SLDVec
imprint (Succ Zero) (VShape d _) (VShape vi lyti) =
    VShape d (LNest vi lyti)
imprint (Succ n) (VShape d lyt) (VShape vi lyti)  =
    VShape d (implantInnerVec n lyt vi lyti)
imprint _          _                   _          =
    $impossible

implantInnerVec :: Nat -> Layout SLDVec -> SLDVec -> Layout SLDVec -> Layout SLDVec
implantInnerVec (Succ Zero) (LNest d _)   vi lyti   =
    LNest d $ LNest vi lyti
implantInnerVec (Succ n)      (LNest d lyt) vi lyti =
    LNest d $ implantInnerVec n lyt vi lyti
implantInnerVec _          _            _  _        =
    $impossible

--------------------------------------------------------------------------------
-- Vectorization Helper Functions

appLayout :: v
          -> (v -> SLDVec -> Build SL (SLDVec, v))
          -> Layout SLDVec
          -> Build SL (Layout SLDVec)
appLayout _ _ LCol = return LCol
appLayout v appVec (LNest d l) = do
    (d', v') <- appVec v d
    l'       <- appLayout v' appVec l
    return $ LNest d' l'
appLayout v appVec (LTuple ls) =
    LTuple <$> mapM (appLayout v appVec) ls

filterLayout :: SLFVec -> Layout SLDVec -> Build SL (Layout SLDVec)
filterLayout v = appLayout v vlAppFilter

repLayout :: SLRVec -> Layout SLDVec -> Build SL (Layout SLDVec)
repLayout v = appLayout v vlAppRep

sortLayout :: SLSVec -> Layout SLDVec -> Build SL (Layout SLDVec)
sortLayout v = appLayout v vlAppSort

rekeyLayout :: SLKVec -> Layout SLDVec -> Build SL (Layout SLDVec)
rekeyLayout v = appLayout v vlAppKey

-- | Apply a rekeying vector to the outermost nested vectors in the
-- layout.
rekeyOuter :: SLKVec -> Layout SLDVec -> Build SL (Layout SLDVec)
rekeyOuter _ LCol          = return LCol
rekeyOuter r (LNest q lyt) = LNest <$> (fst <$> vlAppKey r q) <*> pure lyt
rekeyOuter r (LTuple lyts) = LTuple <$> mapM (rekeyOuter r) lyts

-- | Traverse a layout and append all nested vectors that are
-- encountered.
appendLayout :: Layout SLDVec -> Layout SLDVec -> Build SL (Layout SLDVec)
appendLayout LCol LCol = return LCol
-- Append two nested vectors
appendLayout (LNest dv1 lyt1) (LNest dv2 lyt2) = do
    -- Append the current vectors
    (dv12, kv1, kv2) <- vlAppend dv1 dv2
    -- Propagate position changes to descriptors of any inner vectors
    lyt1'       <- rekeyOuter kv1 lyt1
    lyt2'       <- rekeyOuter kv2 lyt2
    -- Append the layouts, i.e. actually append all inner vectors
    lyt'        <- appendLayout lyt1' lyt2'
    return $ LNest dv12 lyt'
appendLayout (LTuple lyts1) (LTuple lyts2) =
    LTuple <$> zipWithM appendLayout lyts1 lyts2
appendLayout _ _ = $impossible
