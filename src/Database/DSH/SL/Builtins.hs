{-# LANGUAGE OverloadedLists  #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TemplateHaskell  #-}

-- | Vectorising constructor functions that implement FKL primitives
-- using SL operators.
module Database.DSH.SL.Builtins where

import           Control.Applicative
import           Control.Monad
import qualified Data.List                      as List
import           Data.List.NonEmpty             (NonEmpty ((:|)))
import qualified Data.List.NonEmpty             as N
import           Data.Semigroup                 ((<>))
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
import           Database.DSH.SL.Construct
import           Database.DSH.SL.Lang           (TSL)

{-# ANN module "HLint: ignore Reduce duplication" #-}

--------------------------------------------------------------------------------
-- Construction of not-lifted primitives

dist ::  Shape DVec -> Shape DVec -> Build TSL (Shape DVec)
dist (VShape dv lyt) (VShape dvo _) = do
    (prodVec, rv)    <- slReplicateVector dv dvo

    -- The outer vector does not have columns, it only describes the
    -- shape.
    outerVec         <- slProject TIndex dvo

    -- Replicate any inner vectors
    lyt'             <- repLayout rv lyt

    return $ VShape outerVec (LNest prodVec lyt')

concat :: Shape DVec -> Build TSL (Shape DVec)
concat (VShape _ (LNest q lyt)) = VShape <$> slUnsegment q <*> pure lyt
concat _e                       = $impossible

combine :: Shape DVec -> Shape DVec -> Shape DVec -> Build TSL (Shape DVec)
combine (VShape dvb LCol) (VShape dv1 lyt1) (VShape dv2 lyt2) = do
    (dv, kv1, kv2) <- slCombine dvb dv1 dv2
    lyt1'          <- rekeyLayout kv1 lyt1
    lyt2'          <- rekeyLayout kv2 lyt2
    lyt'           <- appendLayout lyt1' lyt2'
    return $ VShape dv lyt'
combine _ _ _ = $impossible

restrict :: Shape DVec -> Build TSL (Shape DVec)
restrict (VShape dv (LTuple [l, LCol])) = do
    -- Filter the vector according to the boolean column
    (dv', fv) <- slSelect (TTupElem (Next First) TInput) dv

    -- After the selection, discard the boolean column
    dv''      <- slProject (TTupElem First TInput) dv'

    -- Filter any inner vectors
    l'        <- filterLayout fv l
    return $ VShape dv'' l'
restrict _ = $impossible

--------------------------------------------------------------------------------
-- Construction of lifted primitives

constLyt :: VecVal -> Layout a
constLyt (VVTuple vs) = LTuple $ map constLyt vs
constLyt (VVScalar _) = LCol
constLyt VTIndex      = LCol

rep :: VecVal -> Shape DVec -> Build TSL (Shape DVec)
rep val (VShape dv _) = do
    dv' <- slProject (valExpr val) dv
    return (VShape dv' (constLyt val))

onlyL :: Shape DVec -> Build TSL (Shape DVec)
onlyL (VShape dvo (LNest dvi lyt)) = do
    (dv, kv) <- slUnboxSng dvo dvi
    lyt'     <- rekeyLayout kv lyt
    return $ VShape dv lyt'
onlyL _                           = $impossible

binOpL :: L.ScalarBinOp -> Shape DVec -> Shape DVec -> Build TSL (Shape DVec)
binOpL o (VShape dv1 _) (VShape dv2 _) = do
    da <- slAlign dv1 dv2
    dv <- slProject (TBinApp o (TTupElem First TInput) (TTupElem (Next First) TInput)) da
    return $ VShape dv LCol

restrictL :: Shape DVec -> Build TSL (Shape DVec)
restrictL (VShape qo (LNest dv (LTuple [l, LCol]))) = do
    -- Filter the vector according to the boolean column
    (dv', fv) <- slSelect (TTupElem (Next First) TInput) dv

    -- After the selection, discard the boolean column
    dv''      <- slProject (TTupElem First TInput) dv'

    -- Filter any inner vectors
    l'        <- filterLayout fv l
    return $ VShape qo (LNest dv'' l')
restrictL _ = $impossible

combineL :: Shape DVec -> Shape DVec -> Shape DVec -> Build TSL (Shape DVec)
combineL (VShape qo (LNest dvb LCol))
         (VShape _ (LNest dv1 lyt1))
         (VShape _ (LNest dv2 lyt2)) = do
    (dv, kv1, kv2) <- slCombine dvb dv1 dv2
    lyt1'          <- rekeyLayout kv1 lyt1
    lyt2'          <- rekeyLayout kv2 lyt2
    lyt'           <- appendLayout lyt1' lyt2'
    return $ VShape qo (LNest dv lyt')
combineL _ _ _ = $impossible

zipL :: Shape DVec -> Shape DVec -> Build TSL (Shape DVec)
zipL (VShape d1 (LNest q1 lyt1)) (VShape _ (LNest q2 lyt2)) = do
    (q', r1, r2) <- slZip q1 q2
    lyt1'        <- repLayout r1 lyt1
    lyt2'        <- repLayout r2 lyt2
    return $ VShape d1 (LNest q' $ LTuple [lyt1', lyt2'])
zipL _ _ = $impossible

cartProductL :: Shape DVec -> Shape DVec -> Build TSL (Shape DVec)
cartProductL (VShape dvo1 (LNest dvi1 lyt1)) (VShape _ (LNest dvi2 lyt2)) = do
    (dv, rv1, rv2) <- slCartProduct dvi1 dvi2
    lyt1'        <- repLayout rv1 lyt1
    lyt2'        <- repLayout rv2 lyt2
    return $ VShape dvo1 (LNest dv $ LTuple [lyt1', lyt2'])
cartProductL _ _ = $impossible

thetaJoinL :: L.JoinPredicate L.ScalarExpr -> Shape DVec -> Shape DVec -> Build TSL (Shape DVec)
thetaJoinL joinPred (VShape dvo1 (LNest dvi1 lyt1)) (VShape _ (LNest dvi2 lyt2)) = do
    (dvi, rv1, rv2) <- slThetaJoin joinPred dvi1 dvi2
    lyt1'           <- repLayout rv1 lyt1
    lyt2'           <- repLayout rv2 lyt2
    return $ VShape dvo1 (LNest dvi $ LTuple [lyt1', lyt2'])
thetaJoinL _ _ _ = $impossible

-- △^L :: [[a]] -> [[b]] -> [[(a, [(a, b)])]]
nestJoinL :: L.JoinPredicate L.ScalarExpr -> Shape DVec -> Shape DVec -> Build TSL (Shape DVec)
nestJoinL joinPred (VShape dvo1 (LNest dvi1 lyt1)) (VShape _ (LNest dvi2 lyt2)) = do
    (dvi, rv1, rv2) <- slNestJoin joinPred dvi1 dvi2
    dvm             <- slProject (TMkTuple [TInput, TIndex]) dvi1
    lyt1'           <- repLayout rv1 lyt1
    lyt2'           <- repLayout rv2 lyt2
    let lyt  = LTuple [lyt1', lyt2']
    return $ VShape dvo1 (LNest dvm (LTuple [lyt1, LNest dvi lyt]))
nestJoinL _ _ _ = $impossible

groupJoinL :: L.JoinPredicate L.ScalarExpr
           -> L.NE (AggrFun TExpr)
           -> Shape DVec
           -> Shape DVec
           -> Build TSL (Shape DVec)
groupJoinL joinPred afuns (VShape dvo1 (LNest dvi1 lyt1)) (VShape _ (LNest dvi2 _)) = do
    dv <- slGroupJoin joinPred afuns dvi1 dvi2
    return $ VShape dvo1 (LNest dv (LTuple (lyt1 : map (const LCol) (N.toList $ L.getNE afuns))))
groupJoinL _ _ _ _ = $impossible

semiJoinL :: L.JoinPredicate L.ScalarExpr -> Shape DVec -> Shape DVec -> Build TSL (Shape DVec)
semiJoinL joinPred (VShape dvo1 (LNest dvi1 lyt1)) (VShape _ (LNest dvi2 _)) = do
    (dv, fv) <- slSemiJoin joinPred dvi1 dvi2
    lyt1'    <- filterLayout fv lyt1
    return $ VShape dvo1 (LNest dv lyt1')
semiJoinL _ _ _ = $impossible

antiJoinL :: L.JoinPredicate L.ScalarExpr -> Shape DVec -> Shape DVec -> Build TSL (Shape DVec)
antiJoinL joinPred (VShape dvo1 (LNest dvi1 lyt1)) (VShape _ (LNest dvi2 _)) = do
    (dv, fv) <- slAntiJoin joinPred dvi1 dvi2
    lyt1'    <- filterLayout fv lyt1
    return $ VShape dvo1 (LNest dv lyt1')
antiJoinL _ _ _ = $impossible

nubL ::  Shape DVec -> Build TSL (Shape DVec)
nubL (VShape d (LNest q lyt)) =  VShape d <$> (LNest <$> slUnique q <*> pure lyt)
nubL _ = $impossible

numberL ::  Shape DVec -> Build TSL (Shape DVec)
numberL (VShape d (LNest q lyt)) =
    VShape d <$> (LNest <$> slNumber q
                        <*> pure (LTuple [lyt, LCol]))
numberL _ = $impossible

appendL ::  Shape DVec -> Shape DVec -> Build TSL (Shape DVec)
appendL (VShape d lyt1) (VShape _ lyt2) = VShape d <$> appendLayout lyt1 lyt2

reverseL ::  Shape DVec -> Build TSL (Shape DVec)
reverseL (VShape dvo (LNest dvi lyt)) = do
    (dv, sv) <- slReverse dvi
    lyt'     <- sortLayout sv lyt
    return (VShape dvo (LNest dv lyt'))
reverseL _ = $impossible

sortL ::  Shape DVec -> Build TSL (Shape DVec)
sortL (VShape dvo (LNest dvi (LTuple [xl, _]))) = do
    -- Sort by all sorting columns from the right tuple component
    (sortedVec, sv) <- slSort (TTupElem (Next First) TInput) dvi

    -- After sorting, discard the sorting criteria columns
    resVec          <- slProject (TTupElem First TInput) sortedVec
    xl'             <- sortLayout sv xl
    return $ VShape dvo (LNest resVec xl')
sortL _ = $impossible

groupL ::  Shape DVec -> Build TSL (Shape DVec)
groupL (VShape dvo (LNest dvi (LTuple [xl, gl]))) = do
    (dvo', dvi', rv) <- slGroup (TTupElem (Next First) TInput) dvi

    -- Discard the grouping columns in the inner vector
    dvi''            <- slProject (TTupElem First TInput) dvi'
    dvo''            <- slProject (TMkTuple [TInput, TIndex]) dvo'

    xl'              <- sortLayout rv xl
    return $ VShape dvo (LNest dvo'' (LTuple [gl, LNest dvi'' xl']))
groupL _ = $impossible

groupaggL :: L.NE (AggrFun TExpr) -> Shape DVec -> Build TSL (Shape DVec)
groupaggL as (VShape dvo (LNest dvi (LTuple [xl, gl]))) = do
    -- Create the vector for groups
    (_, dvg, rv) <- slGroup TInpSecond dvi
    dvg'         <- slProject (TTupElem First TInput) dvg
    xl'          <- sortLayout rv xl

    -- Create the outer sector describing the group structure
    dva          <- slGroupAgg as TInpSecond dvi
    let proj = case L.getNE as of
                   _ :| [] -> TMkTuple [TInpFirst, TIndex, TSecond TInpFirst, TInpSecond]
                   _       -> let aProj = fmap (\i -> TTupElem (intIndex i) (TSecond TInpSecond)) [1..length as]
                              in TMkTuple $ [TInpFirst, TIndex] <> aProj
    dv             <- slProject proj dva
    let aggLyts = map (const LCol) [1..length as]
    return $ VShape dvo (LNest dv (LTuple $ [gl, LNest dvg' xl'] ++ aggLyts))
groupaggL _ _ = $impossible

concatL ::  Shape DVec -> Build TSL (Shape DVec)
concatL (VShape vo (LNest vm (LNest vi l))) = do
    vm' <- slMergeSeg vm vi
    return $ VShape vo (LNest vm' l)
concatL _ = $impossible

lengthL ::  Shape DVec -> Build TSL (Shape DVec)
lengthL (VShape q (LNest qi _)) = do
    ls  <- slFold AggrCount qi
    lsu <- defaultUnboxOp AggrCount q ls
    lp  <- slProject (TTupElem (Next First) TInput) lsu
    return $ VShape lp LCol
lengthL _ = $impossible

outer ::  Shape DVec -> Build TSL DVec
outer (VShape q _)        = return q

aggrL :: (TExpr -> AggrFun TExpr) -> Shape DVec -> Build TSL (Shape DVec)
aggrL afun (VShape d (LNest q LCol)) = do
    qr <- slFold (afun TInput) q
    qu <- defaultUnboxOp (afun TInput) d qr
    qp <- slProject (TTupElem (Next First) TInput) qu
    return $ VShape qp LCol
aggrL _ _ = $impossible

distL ::  Shape DVec -> Shape DVec -> Build TSL (Shape DVec)
distL (VShape dv1 lyt1) (VShape dvo2 (LNest dvi2 lyt2)) = do
    (dv, rv)        <- slReplicateNest dv1 dvi2
    lyt1'           <- repLayout rv lyt1
    let lyt = LTuple [lyt1', lyt2]
    VShape dv' lytf <- tupElemL First $ VShape dv lyt
    return $ VShape dvo2 (LNest dv' lytf)
distL _e1 _e2 = $impossible

tupleL :: [Shape DVec] -> Build TSL (Shape DVec)
tupleL (s : ss) = do
    -- Construct a right-deep tree of aligns to bring all vectors together
    (q, lyts, es) <- tupleVectors (s :| ss)
    -- Flatten the resulting nested pair structure
    qd            <- slProject (TMkTuple es) q
    return $ VShape qd (LTuple lyts)
tupleL _ = $impossible

tupElemL :: TupleIndex -> Shape DVec -> Build TSL (Shape DVec)
tupElemL i (VShape q (LTuple lyts)) = do
    let lyt = lyts !! (tupleIndex i - 1)
    proj <- slProject (TTupElem i TInput) q
    return $ VShape proj lyt
tupElemL i s = error $ "tupElemL: " ++ show i ++ " " ++ show s

singletonL :: Shape DVec -> Build TSL (Shape DVec)
singletonL (VShape q lyt) = do
    dvo <- slProject TIndex q
    dvi <- slSegment q
    return $ VShape dvo (LNest dvi lyt)

--------------------------------------------------------------------------------
-- Construction of base tables and literal tables

-- | Create a SL reference to a base table.
dbTable :: String -> L.BaseTableSchema -> Build TSL (Shape DVec)
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

shredList :: [L.Val] -> Layout (PType, S.Seq SegD) -> (S.Seq VecVal, Layout (PType, S.Seq SegD))
shredList vs lyt = List.foldl' go (S.empty, lyt) vs
  where
    go (vvs, l) v = let (vv, l') = shredValue v l
                    in (vvs S.|> vv, l')

shredValue :: L.Val -> Layout (PType, S.Seq SegD) -> (VecVal, Layout (PType, S.Seq SegD))
shredValue (L.ListV vs)  (LNest (ty, segs) lyt) =
    let (seg, lyt') = shredList vs lyt
    in (VTIndex, LNest (ty, segs S.|> seg) lyt')
shredValue (L.TupleV vs) (LTuple lyts)          =
    let (vvs, ls) = unzip $ zipWith shredValue vs lyts
    in (VVTuple vvs, LTuple ls)
shredValue (L.ScalarV v) LCol                   =
    (VVScalar v, LCol)
shredValue _ _ = $impossible

shredType :: Type -> Layout (PType, S.Seq SegD)
shredType (ScalarT _) = LCol
shredType (TupleT ts) = LTuple $ map shredType ts
shredType (ListT t)   = LNest (payloadType t, S.empty) (shredType t)

payloadType :: Type -> PType
payloadType (ScalarT t) = PScalarT t
payloadType (TupleT ts) = PTupleT (N.fromList $ map payloadType ts)
payloadType (ListT _)   = PIndexT

literalVectors :: Layout (PType, S.Seq SegD) -> Build TSL (Layout DVec)
literalVectors lyt = traverse go lyt
  where
    go (ty, segs) = slLit (ty, Segs segs)

literalShape :: Shape (PType, S.Seq SegD) -> Build TSL (Shape DVec)
literalShape (VShape (ty, segs) lyt) = do
    let seg = if S.null segs then $impossible else S.index segs 0
    shapeVec <- slLit (ty, UnitSeg seg)
    vecLyt   <- literalVectors lyt
    return $ VShape shapeVec vecLyt

shredLiteral :: Type -> L.Val -> Build TSL (Shape DVec)
shredLiteral (ListT t) (L.ListV vs) = literalShape $ VShape (payloadType t, S.singleton seg) lyt
  where
    initLyt    = shredType t
    (seg, lyt) = shredList vs initLyt
shredLiteral _ _ = $impossible

--------------------------------------------------------------------------------
-- Helper functions for zipping/tuple construction

-- | Simply align a list of shapes and collect their layouts.
tupleVectors :: NonEmpty (Shape DVec) -> Build TSL (DVec, [Layout DVec], NonEmpty TExpr)
tupleVectors (VShape q1 lyt1 :| [])       = return (q1, [lyt1], pure TInput)
tupleVectors (VShape q1 lyt1 :| (s : ss)) = do
    (q, lyts, es) <- tupleVectors $ s :| ss
    qz' <- slAlign q1 q
    return (qz', lyt1 : lyts, TInpFirst N.<| fmap (mergeExpr TInpSecond) es)

--------------------------------------------------------------------------------
-- Vectorization Helper Functions

appLayout :: v
          -> (v -> DVec -> Build TSL (DVec, v))
          -> Layout DVec
          -> Build TSL (Layout DVec)
appLayout _ _ LCol = return LCol
appLayout v appVec (LNest d l) = do
    (d', v') <- appVec v d
    l'       <- appLayout v' appVec l
    return $ LNest d' l'
appLayout v appVec (LTuple ls) =
    LTuple <$> mapM (appLayout v appVec) ls

filterLayout :: FVec -> Layout DVec -> Build TSL (Layout DVec)
filterLayout v = appLayout v slAppFilter

repLayout :: RVec -> Layout DVec -> Build TSL (Layout DVec)
repLayout v = appLayout v slAppRep

sortLayout :: SVec -> Layout DVec -> Build TSL (Layout DVec)
sortLayout v = appLayout v slAppSort

-- | Apply a rekeying vector to the outermost nested vectors in the
-- layout.
rekeyLayout :: KVec -> Layout DVec -> Build TSL (Layout DVec)
rekeyLayout _ LCol          = return LCol
rekeyLayout r (LNest q lyt) = LNest <$> (slAppKey r q) <*> pure lyt
rekeyLayout r (LTuple lyts) = LTuple <$> mapM (rekeyLayout r) lyts

-- | Traverse a layout and append all nested vectors that are
-- encountered.
appendLayout :: Layout DVec -> Layout DVec -> Build TSL (Layout DVec)
appendLayout LCol LCol = return LCol
-- Append two nested vectors
appendLayout (LNest dv1 lyt1) (LNest dv2 lyt2) = do
    -- Append the current vectors
    (dv12, kv1, kv2) <- slAppend dv1 dv2
    -- Propagate position changes to descriptors of any inner vectors
    lyt1'       <- rekeyLayout kv1 lyt1
    lyt2'       <- rekeyLayout kv2 lyt2
    -- Append the layouts, i.e. actually append all inner vectors
    lyt'        <- appendLayout lyt1' lyt2'
    return $ LNest dv12 lyt'
appendLayout (LTuple lyts1) (LTuple lyts2) =
    LTuple <$> zipWithM appendLayout lyts1 lyts2
appendLayout _ _ = $impossible

defaultUnboxOp :: AggrFun TExpr -> DVec -> DVec -> Build TSL DVec
defaultUnboxOp (AggrSum t _)         = slUnboxDefault (TConstant $ sumDefault t)
  where
    sumDefault IntT     = L.IntV 0
    sumDefault DecimalT = L.DecimalV 0
    sumDefault DoubleT  = L.DoubleV 0
    sumDefault _        = error "SL.Builtins.defaultUnboxOp: not a numeric type"
defaultUnboxOp (AggrAny _)           = slUnboxDefault (TConstant $ L.BoolV False)
defaultUnboxOp (AggrAll _)           = slUnboxDefault (TConstant $ L.BoolV True)
defaultUnboxOp AggrCount             = slUnboxDefault (TConstant $ L.IntV 0)
defaultUnboxOp (AggrCountDistinct _) = slUnboxDefault (TConstant $ L.IntV 0)
defaultUnboxOp _                     = \v1 v2 -> fst <$> slUnboxSng v1 v2
