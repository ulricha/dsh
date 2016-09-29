{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TemplateHaskell  #-}

-- | Vectorising constructor functions that implement FKL primitives
-- using SL operators.
module Database.DSH.SL.Builtins where

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
import           Database.DSH.SL.Construct

{-# ANN module "HLint: ignore Reduce duplication" #-}

--------------------------------------------------------------------------------
-- Construction of not-lifted primitives

dist ::  Shape DVec -> Shape DVec -> Build SL (Shape DVec)
dist (VShape dv lyt) (VShape dvo _) = do
    (prodVec, rv)    <- slReplicateVector dv dvo

    -- The outer vector does not have columns, it only describes the
    -- shape.
    outerVec         <- slProject [] dvo

    -- Replicate any inner vectors
    lyt'             <- repLayout rv lyt

    return $ VShape outerVec (LNest prodVec lyt')
dist _ _ = $impossible

concat :: Shape DVec -> Build SL (Shape DVec)
concat (VShape _ (LNest q lyt)) = VShape <$> slUnsegment q <*> pure lyt
concat _e                       = $impossible

combine :: Shape DVec -> Shape DVec -> Shape DVec -> Build SL (Shape DVec)
combine (VShape dvb LCol) (VShape dv1 lyt1) (VShape dv2 lyt2) = do
    (dv, kv1, kv2) <- slCombine dvb dv1 dv2
    lyt1'          <- rekeyOuter kv1 lyt1
    lyt2'          <- rekeyOuter kv2 lyt2
    lyt'           <- appendLayout lyt1' lyt2'
    return $ VShape dv lyt'
combine _ _ _ = $impossible

restrict :: Shape DVec -> Build SL (Shape DVec)
restrict (VShape dv (LTuple [l, LCol])) = do
    let leftWidth = columnsInLayout l
        predicate = Column $ leftWidth + 1

    -- Filter the vector according to the boolean column
    (dv', fv) <- slSelect predicate dv

    -- After the selection, discard the boolean column
    dv''      <- slProject (map Column [1..leftWidth]) dv'

    -- Filter any inner vectors
    l'        <- filterLayout fv l
    return $ VShape dv'' l'
restrict _ = $impossible

--------------------------------------------------------------------------------
-- Construction of lifted primitives

extL :: L.ScalarVal -> Shape DVec -> Build SL (Shape DVec)
extL val (VShape dvo (LNest dvi lyt)) = do
    let w = columnsInLayout lyt
    dvi' <- slProject ([ Column c | c <- [1..w]] ++ [Constant val]) dvi
    return (VShape dvo (LNest dvi' (LTuple [lyt, LCol])))
extL _ _ = $impossible

onlyL :: Shape DVec -> Build SL (Shape DVec)
onlyL (VShape dvo (LNest dvi lyt)) = do
    (dv, kv) <- slUnboxSng dvo dvi
    lyt'     <- rekeyOuter kv lyt
    return $ VShape dv lyt'
onlyL _                           = $impossible

binOpL :: L.ScalarBinOp -> Shape DVec -> Shape DVec -> Build SL (Shape DVec)
binOpL o (VShape dv1 _) (VShape dv2 _) = do
    dv <- slProject [BinApp o (Column 1) (Column 2)] =<< slAlign dv1 dv2
    return $ VShape dv LCol
binOpL _ _ _ = $impossible

restrictL :: Shape DVec -> Build SL (Shape DVec)
restrictL (VShape qo (LNest dv (LTuple [l, LCol]))) = do
    let leftWidth = columnsInLayout l
        predicate = Column $ leftWidth + 1

    -- Filter the vector according to the boolean column
    (dv', fv) <- slSelect predicate dv

    -- After the selection, discard the boolean column
    dv''      <- slProject (map Column [1..leftWidth]) dv'

    -- Filter any inner vectors
    l'        <- filterLayout fv l
    return $ VShape qo (LNest dv'' l')
restrictL _ = $impossible

combineL :: Shape DVec -> Shape DVec -> Shape DVec -> Build SL (Shape DVec)
combineL (VShape qo (LNest dvb LCol))
         (VShape _ (LNest dv1 lyt1))
         (VShape _ (LNest dv2 lyt2)) = do
    (dv, kv1, kv2) <- slCombine dvb dv1 dv2
    lyt1'          <- rekeyOuter kv1 lyt1
    lyt2'          <- rekeyOuter kv2 lyt2
    lyt'           <- appendLayout lyt1' lyt2'
    return $ VShape qo (LNest dv lyt')
combineL _ _ _ = $impossible

zipL :: Shape DVec -> Shape DVec -> Build SL (Shape DVec)
zipL (VShape d1 (LNest q1 lyt1)) (VShape _ (LNest q2 lyt2)) = do
    (q', r1, r2) <- slZip q1 q2
    lyt1'        <- repLayout r1 lyt1
    lyt2'        <- repLayout r2 lyt2
    return $ VShape d1 (LNest q' $ LTuple [lyt1', lyt2'])
zipL _ _ = $impossible

cartProductL :: Shape DVec -> Shape DVec -> Build SL (Shape DVec)
cartProductL (VShape dvo1 (LNest dvi1 lyt1)) (VShape _ (LNest dvi2 lyt2)) = do
    (dv, rv1, rv2) <- slCartProduct dvi1 dvi2
    lyt1'        <- repLayout rv1 lyt1
    lyt2'        <- repLayout rv2 lyt2
    return $ VShape dvo1 (LNest dv $ LTuple [lyt1', lyt2'])
cartProductL _ _ = $impossible

thetaJoinL :: L.JoinPredicate L.ScalarExpr -> Shape DVec -> Shape DVec -> Build SL (Shape DVec)
thetaJoinL joinPred (VShape dvo1 (LNest dvi1 lyt1)) (VShape _ (LNest dvi2 lyt2)) = do
    (dvi, rv1, rv2) <- slThetaJoin joinPred dvi1 dvi2
    lyt1'           <- repLayout rv1 lyt1
    lyt2'           <- repLayout rv2 lyt2
    return $ VShape dvo1 (LNest dvi $ LTuple [lyt1', lyt2'])
thetaJoinL _ _ _ = $impossible

-- △^L :: [[a]] -> [[b]] -> [[(a, [(a, b)])]]
nestJoinL :: L.JoinPredicate L.ScalarExpr -> Shape DVec -> Shape DVec -> Build SL (Shape DVec)
nestJoinL joinPred (VShape dvo1 (LNest dvi1 lyt1)) (VShape _ (LNest dvi2 lyt2)) = do
    (dv, rv1, rv2) <- slNestJoin joinPred dvi1 dvi2
    lyt1'          <- repLayout rv1 lyt1
    lyt2'          <- repLayout rv2 lyt2
    let lyt  = LTuple [lyt1', lyt2']
    return $ VShape dvo1 (LNest dvi1 (LTuple [lyt1, LNest dv lyt]))
nestJoinL _ _ _ = $impossible

groupJoinL :: L.JoinPredicate L.ScalarExpr
           -> L.NE AggrFun
           -> Shape DVec
           -> Shape DVec
           -> Build SL (Shape DVec)
groupJoinL joinPred afuns (VShape dvo1 (LNest dvi1 lyt1)) (VShape _ (LNest dvi2 _)) = do
    dv <- slGroupJoin joinPred afuns dvi1 dvi2
    return $ VShape dvo1 (LNest dv (LTuple (lyt1 : map (const LCol) (N.toList $ L.getNE afuns))))
groupJoinL _ _ _ _ = $impossible

semiJoinL :: L.JoinPredicate L.ScalarExpr -> Shape DVec -> Shape DVec -> Build SL (Shape DVec)
semiJoinL joinPred (VShape dvo1 (LNest dvi1 lyt1)) (VShape _ (LNest dvi2 _)) = do
    (dv, fv) <- slSemiJoin joinPred dvi1 dvi2
    lyt1'    <- filterLayout fv lyt1
    return $ VShape dvo1 (LNest dv lyt1')
semiJoinL _ _ _ = $impossible

antiJoinL :: L.JoinPredicate L.ScalarExpr -> Shape DVec -> Shape DVec -> Build SL (Shape DVec)
antiJoinL joinPred (VShape dvo1 (LNest dvi1 lyt1)) (VShape _ (LNest dvi2 _)) = do
    (dv, fv) <- slAntiJoin joinPred dvi1 dvi2
    lyt1'    <- filterLayout fv lyt1
    return $ VShape dvo1 (LNest dv lyt1')
antiJoinL _ _ _ = $impossible

nubL ::  Shape DVec -> Build SL (Shape DVec)
nubL (VShape d (LNest q lyt)) =  VShape d <$> (LNest <$> slUnique q <*> pure lyt)
nubL _ = $impossible

numberL ::  Shape DVec -> Build SL (Shape DVec)
numberL (VShape d (LNest q lyt)) =
    VShape d <$> (LNest <$> slNumber q
                        <*> pure (LTuple [lyt, LCol]))
numberL _ = $impossible

appendL ::  Shape DVec -> Shape DVec -> Build SL (Shape DVec)
appendL (VShape d lyt1) (VShape _ lyt2) = VShape d <$> appendLayout lyt1 lyt2
appendL _ _ = $impossible

reverseL ::  Shape DVec -> Build SL (Shape DVec)
reverseL (VShape dvo (LNest dvi lyt)) = do
    (dv, sv) <- slReverse dvi
    lyt'     <- sortLayout sv lyt
    return (VShape dvo (LNest dv lyt'))
reverseL _ = $impossible

sortL ::  Shape DVec -> Build SL (Shape DVec)
sortL (VShape dvo (LNest dvi (LTuple [xl, sl]))) = do
    let leftWidth  = columnsInLayout xl
        rightWidth = columnsInLayout sl

        sortExprs = map Column [leftWidth+1..leftWidth+rightWidth]

    -- Sort by all sorting columns from the right tuple component
    (sortedVec, sv) <- slSort sortExprs dvi

    -- After sorting, discard the sorting criteria columns
    resVec          <- slProject (map Column [1..leftWidth]) sortedVec
    xl'             <- sortLayout sv xl
    return $ VShape dvo (LNest resVec xl')
sortL _ = $impossible

groupL ::  Shape DVec -> Build SL (Shape DVec)
groupL (VShape dvo (LNest dvi (LTuple [xl, gl]))) = do
    let leftWidth  = columnsInLayout xl
        rightWidth = columnsInLayout gl

        groupExprs = map Column [leftWidth+1..leftWidth+rightWidth]

    (dvo', dvi', rv) <- slGroup groupExprs dvi

    -- Discard the grouping columns in the inner vector
    dvi''            <- slProject (map Column [1..leftWidth]) dvi'

    xl'              <- sortLayout rv xl
    return $ VShape dvo (LNest dvo' (LTuple [gl, LNest dvi'' xl']))
groupL _ = $impossible

concatL ::  Shape DVec -> Build SL (Shape DVec)
concatL (VShape d (LNest d' vs)) = do
    p   <- slUnboxKey d'
    vs' <- rekeyOuter p vs
    return $ VShape d vs'
concatL _ = $impossible

lengthL ::  Shape DVec -> Build SL (Shape DVec)
lengthL (VShape q (LNest qi _)) = do
    ls  <- slFold AggrCount q qi
    lsu <- fst <$> slUnboxSng q ls
    return $ VShape lsu LCol
lengthL _ = $impossible

outer ::  Shape DVec -> Build SL DVec
outer (SShape _ _)        = $impossible
outer (VShape q _)        = return q

aggrL :: (Expr -> AggrFun) -> Shape DVec -> Build SL (Shape DVec)
aggrL afun (VShape d (LNest q LCol)) = do
    qr <- slFold (afun (Column 1)) d q
    qu <- fst <$> slUnboxSng d qr
    return $ VShape qu LCol
aggrL _ _ = $impossible

distL ::  Shape DVec -> Shape DVec -> Build SL (Shape DVec)
distL (VShape dv1 lyt1) (VShape dvo2 (LNest dvi2 lyt2)) = do
    (dv, rv)        <- slReplicateNest dv1 dvi2
    lyt1'           <- repLayout rv lyt1
    let lyt = LTuple [lyt1', lyt2]
    VShape dv' lytf <- tupElemL First $ VShape dv lyt
    return $ VShape dvo2 (LNest dv' lytf)
distL _e1 _e2 = $impossible

tupleL :: [Shape DVec] -> Build SL (Shape DVec)
tupleL shapes@(_ : _) = do
    (q, lyts) <- alignVectors shapes
    return $ VShape q (LTuple lyts)
tupleL _ = $impossible

tupElemL :: TupleIndex -> Shape DVec -> Build SL (Shape DVec)
tupElemL i (VShape q (LTuple lyts)) = do
    let (lyt', cols) = projectColumns i lyts
    proj <- slProject (map Column cols) q
    return $ VShape proj lyt'
tupElemL _ _ = $impossible

singletonL :: Shape DVec -> Build SL (Shape DVec)
singletonL (VShape q lyt) = do
    dvo <- slProject [] q
    dvi <- slSegment q
    return $ VShape dvo (LNest dvi lyt)
singletonL _ = $impossible

--------------------------------------------------------------------------------
-- Construction of base tables and literal tables

-- | Create a SL reference to a base table.
dbTable :: String -> L.BaseTableSchema -> Build SL (Shape DVec)
dbTable n schema = do
    tab <- slTableRef n schema
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
toColumns :: Type -> [L.Val] -> Build SL ([ScalarType], [Column], Layout DVec)
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
toVector :: Type -> [L.Val] -> Build SL (DVec, Layout DVec)
toVector t ls = do
    -- Concatenate the elements of all inner lists
    let innerLists = map fromList ls
        allElems   = List.concat innerLists
        innerLens  = map length innerLists
    (tys, cols, lyt) <- toColumns t allElems
    let segs = chopSegments innerLens cols
    litNode <- slLit (tys, SegFrame $ length allElems, Segs segs)
    return (litNode, lyt)

-- | Shred a literal value into flat vectors.
shredLiteral ::  Type -> [L.Val] -> Build SL (Shape DVec)
shredLiteral (ListT t) es = do
    (tys, cols, lyt) <- toColumns t es
    litNode <- slLit (tys, SegFrame $ length es, UnitSeg cols)
    return $ VShape litNode lyt
shredLiteral _ _ = $impossible

--------------------------------------------------------------------------------
-- Helper functions for zipping/tuple construction

-- | Simply align a list of shapes and collect their layouts.
alignVectors :: [Shape DVec] -> Build SL (DVec, [Layout DVec])
alignVectors [VShape q1 lyt1]          = return (q1, [lyt1])
alignVectors (VShape q1 lyt1 : shapes) = do
    (q, lyts) <- alignVectors shapes
    qz' <- slAlign q1 q
    return (qz', lyt1 : lyts)
alignVectors _ = $impossible

--------------------------------------------------------------------------------
-- Vectorization Helper Functions

appLayout :: v
          -> (v -> DVec -> Build SL (DVec, v))
          -> Layout DVec
          -> Build SL (Layout DVec)
appLayout _ _ LCol = return LCol
appLayout v appVec (LNest d l) = do
    (d', v') <- appVec v d
    l'       <- appLayout v' appVec l
    return $ LNest d' l'
appLayout v appVec (LTuple ls) =
    LTuple <$> mapM (appLayout v appVec) ls

filterLayout :: FVec -> Layout DVec -> Build SL (Layout DVec)
filterLayout v = appLayout v slAppFilter

repLayout :: RVec -> Layout DVec -> Build SL (Layout DVec)
repLayout v = appLayout v slAppRep

sortLayout :: SVec -> Layout DVec -> Build SL (Layout DVec)
sortLayout v = appLayout v slAppSort

rekeyLayout :: KVec -> Layout DVec -> Build SL (Layout DVec)
rekeyLayout v = appLayout v slAppKey

-- | Apply a rekeying vector to the outermost nested vectors in the
-- layout.
rekeyOuter :: KVec -> Layout DVec -> Build SL (Layout DVec)
rekeyOuter _ LCol          = return LCol
rekeyOuter r (LNest q lyt) = LNest <$> (fst <$> slAppKey r q) <*> pure lyt
rekeyOuter r (LTuple lyts) = LTuple <$> mapM (rekeyOuter r) lyts

-- | Traverse a layout and append all nested vectors that are
-- encountered.
appendLayout :: Layout DVec -> Layout DVec -> Build SL (Layout DVec)
appendLayout LCol LCol = return LCol
-- Append two nested vectors
appendLayout (LNest dv1 lyt1) (LNest dv2 lyt2) = do
    -- Append the current vectors
    (dv12, kv1, kv2) <- slAppend dv1 dv2
    -- Propagate position changes to descriptors of any inner vectors
    lyt1'       <- rekeyOuter kv1 lyt1
    lyt2'       <- rekeyOuter kv2 lyt2
    -- Append the layouts, i.e. actually append all inner vectors
    lyt'        <- appendLayout lyt1' lyt2'
    return $ LNest dv12 lyt'
appendLayout (LTuple lyts1) (LTuple lyts2) =
    LTuple <$> zipWithM appendLayout lyts1 lyts2
appendLayout _ _ = $impossible
