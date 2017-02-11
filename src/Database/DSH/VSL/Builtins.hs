{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE OverloadedLists #-}

{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

module Database.DSH.VSL.Builtins where

import           Control.Monad
import qualified Data.List                      as List
import qualified Data.List.NonEmpty             as N
import           Data.List.NonEmpty             (NonEmpty((:|)))
import qualified Data.Sequence                  as S

import           Database.Algebra.Dag.Common

import           Database.DSH.Common.Impossible
import qualified Database.DSH.Common.Lang       as L
import           Database.DSH.Common.Nat
import           Database.DSH.Common.QueryPlan
import qualified Database.DSH.Common.Type       as T
import           Database.DSH.Common.Vector
import           Database.DSH.Common.VectorLang
import           Database.DSH.VSL.Construct     (VSLBuild)
import qualified Database.DSH.VSL.Construct     as C

newtype DataNode = DataNode AlgNode
newtype MapNode = MapNode AlgNode

data SegMap = IDMap
            | UnitMap RVec
            | RMap RVec
            deriving (Show)

data DelayedVec = DelayedVec
    { dvSegMap  :: SegMap
    , dvPhysVec :: DVec
    } deriving (Show)

pattern MatVec :: DVec -> DelayedVec
pattern MatVec v = DelayedVec IDMap v

--------------------------------------------------------------------------------
-- Unary scalar operators

unOpL :: L.ScalarUnOp -> Shape DelayedVec -> VSLBuild TExpr TExpr (Shape DelayedVec)
unOpL o (VShape (DelayedVec m v) LCol) = do
    vp <- C.project (TUnApp o TInput) v
    return $ VShape (DelayedVec m vp) LCol

--------------------------------------------------------------------------------
-- Binary scalar operators

binOpL :: L.ScalarBinOp -> Shape DelayedVec -> Shape DelayedVec -> VSLBuild TExpr TExpr (Shape DelayedVec)
binOpL o (VShape dv1 LCol) (VShape dv2 LCol) = do
    case (dvSegMap dv1, dvSegMap dv2) of
        (RMap m1, RMap _) -> do
            v  <- C.align (dvPhysVec dv1) (dvPhysVec dv2)
            v' <- C.project (TBinApp o (TTupElem First TInput) (TTupElem (Next First) TInput)) v
            return $ VShape (DelayedVec (RMap m1) v') LCol
        (UnitMap m1, UnitMap _) -> do
            v  <- C.align (dvPhysVec dv1) (dvPhysVec dv2)
            v' <- C.project (TBinApp o (TTupElem First TInput) (TTupElem (Next First) TInput)) v
            return $ VShape (DelayedVec (UnitMap m1) v') LCol
        (IDMap, IDMap) -> do
            v  <- C.align (dvPhysVec dv1) (dvPhysVec dv2)
            v' <- C.project (TBinApp o (TTupElem First TInput) (TTupElem (Next First) TInput)) v
            return $ VShape (DelayedVec IDMap v') LCol
        (RMap m1, IDMap) -> do
            -- Materialize the left input
            -- We do not need the replication vector because the layout is flat
            (mv1, _) <- C.materialize m1 (dvPhysVec dv1)
            v        <- C.align mv1 (dvPhysVec dv2)
            v'       <- C.project (TBinApp o (TTupElem First TInput) (TTupElem (Next First) TInput)) v
            return $ VShape (DelayedVec IDMap v') LCol
        (IDMap, RMap m2) -> do
            -- Materialize the right input
            -- We do not need the replication vector because the layout is flat
            (mv2, _) <- C.materialize m2 (dvPhysVec dv2)
            v        <- C.align (dvPhysVec dv1) mv2
            v'       <- C.project (TBinApp o (TTupElem First TInput) (TTupElem (Next First) TInput)) v
            return $ VShape (DelayedVec IDMap v') LCol

--------------------------------------------------------------------------------
-- Tuple indexing

tupElemL :: TupleIndex -> Shape DelayedVec -> VSLBuild TExpr TExpr (Shape DelayedVec)
tupElemL i (VShape dv (LTuple ls)) = do
    let l = ls !! (tupleIndex i - 1)
    vp <- C.project (TTupElem i TInput) (dvPhysVec dv)
    return $ VShape (dv { dvPhysVec = vp }) (l)

--------------------------------------------------------------------------------
-- Singleton list construction

sngL :: Shape DelayedVec -> VSLBuild TExpr TExpr (Shape DelayedVec)
sngL (VShape (DelayedVec m v) l) = do
    vo <- C.project TIndex v
    vi <- C.segment v
    return $ VShape (DelayedVec m vo) (LNest (DelayedVec IDMap vi) l)

--------------------------------------------------------------------------------
-- Aggregation

aggrL :: (TExpr -> AggrFun TExpr) -> Shape DelayedVec -> VSLBuild TExpr TExpr (Shape DelayedVec)
aggrL afun (VShape dvo (LNest dvi _)) = do
    let a = afun TInput
    -- Aggregate the physical segments without considering the segment map.
    va      <- C.aggrseg a (dvPhysVec dvi)
    -- To unbox, we need to materialize the inner vector. Crucially, we
    -- materialize *after* aggregation.
    (vm, _) <- materializeShape (dvi { dvPhysVec = va }) LCol
    vu      <- fst <$> defaultUnboxOp a (dvPhysVec dvo) vm
    vp      <- C.project (TTupElem (Next First) TInput) vu
    return $ VShape (dvo { dvPhysVec = vp }) LCol

defaultUnboxOp :: AggrFun TExpr -> DVec -> DVec -> VSLBuild TExpr TExpr (DVec, RVec)
defaultUnboxOp (AggrSum t _)         = C.unboxdefault (pure $ sumDefault t)
  where
    sumDefault T.IntT = L.IntV 0
    sumDefault T.DecimalT = L.DecimalV 0
    sumDefault T.DoubleT = L.DoubleV 0
defaultUnboxOp (AggrAny _)           = C.unboxdefault (pure $ L.BoolV False)
defaultUnboxOp (AggrAll _)           = C.unboxdefault (pure $ L.BoolV True)
defaultUnboxOp AggrCount             = C.unboxdefault (pure $ L.IntV 0)
defaultUnboxOp (AggrCountDistinct _) = C.unboxdefault (pure $ L.IntV 0)
defaultUnboxOp _                     = C.unboxsng

--------------------------------------------------------------------------------
-- Concatenation

concat :: Shape DelayedVec -> VSLBuild TExpr TExpr (Shape DelayedVec)
concat (VShape _ (LNest dv l)) = do
    (v, l') <- materializeShape dv l
    v'      <- C.unsegment v
    return $ VShape (MatVec v') l'

concatL :: Shape DelayedVec -> VSLBuild TExpr TExpr (Shape DelayedVec)
concatL (VShape dvo (LNest dvi l)) = do
    -- Generate a segment map that merges segments of inner vectors and maps
    -- them to the segment identifiers of 'dvi'
    mm <- C.mergemap (dvPhysVec dvi)
    -- Combine the segment map of the middle vector with the merge map
    mm' <- case dvSegMap dvi of
        IDMap -> return mm
        RMap m -> C.updatemap m mm
        UnitMap m -> C.updatemap m mm
    -- Update the inner segment maps with the merge map to get rid of the middle
    -- vector and align the outer with the inner vectors.
    l' <- updateLayoutMaps (RMap mm') l
    return $ VShape dvo l'

--------------------------------------------------------------------------------
-- Tuple Construction

tupleL :: [Shape DelayedVec] -> VSLBuild TExpr TExpr (Shape DelayedVec)
tupleL shapes =
    case shapes of
        (VShape (DelayedVec (UnitMap m) v) l) : shs
            | all isUnitShape shs -> do
          let (vs, ls) = unzip $ map (\(VShape (DelayedVec _ v') l') -> (v', l')) shs
          (va, es) <- alignVectors $ v :| vs
          vd       <- C.project (TMkTuple es) va
          return $ VShape (DelayedVec (UnitMap m) vd) (LTuple $ l:ls)
        (VShape dv1 l1) : shs -> do
          (v1, l1') <- materializeShape dv1 l1
          (vs, ls)  <- unzip <$> mapM (\(VShape dv l) -> materializeShape dv l) shs
          (va, es)  <- alignVectors $ v1 :| vs
          vd        <- C.project (TMkTuple es) va
          return $ VShape (MatVec vd) (LTuple $ l1' : ls)

alignVectors :: NonEmpty DVec -> VSLBuild TExpr TExpr (DVec, NonEmpty TExpr)
alignVectors (v :| [])        = pure (v, pure TInput)
alignVectors (v :| (v' : vs)) = do
    (vsa, es) <- alignVectors $ v' :| vs
    va        <- C.align v vsa
    pure (va, TInpFirst N.<| fmap (mergeExpr TInpSecond) es)

isUnitShape :: Shape DelayedVec -> Bool
isUnitShape (VShape (DelayedVec (UnitMap _) _) _) = True
isUnitShape _                                     = False

--------------------------------------------------------------------------------
-- Singleton list conversion

onlyL :: Shape DelayedVec -> VSLBuild TExpr TExpr (Shape DelayedVec)
onlyL (VShape dvo (LNest dvi li)) = do
    (vim, lim) <- materializeShape dvi li
    (vu, r) <- C.unboxsng (dvPhysVec dvo) vim
    lim' <- updateLayoutMaps (RMap r) lim
    return $ VShape (dvo { dvPhysVec = vu }) lim'

--------------------------------------------------------------------------------
-- Unary vectorization macros

type UnVectMacro = DelayedVec -> Layout DelayedVec -> VSLBuild TExpr TExpr (DelayedVec, Layout DelayedVec)

--------------------------------------------------------------------------------
-- number

number :: UnVectMacro
number dv l = do
    v <- C.number (dvPhysVec dv)
    return (dv { dvPhysVec = v }, LTuple [l, LCol])

--------------------------------------------------------------------------------
-- distinct

nub :: UnVectMacro
nub dv l = do
    v <- C.distinct (dvPhysVec dv)
    return (dv { dvPhysVec = v }, l)

--------------------------------------------------------------------------------
-- reverse

reverse :: UnVectMacro
reverse dv l = do
    (v, r) <- C.reverse (dvPhysVec dv)
    l'     <- updateLayoutMaps (RMap r) l
    return (dv { dvPhysVec = v }, l')

--------------------------------------------------------------------------------
-- sort

sort :: UnVectMacro
sort dv (LTuple [xl, _]) = do
    -- Sort by all sorting columns from the right tuple component
    (v', r) <- C.sort (TTupElem (Next First) TInput) (dvPhysVec dv)
    -- After sorting, discard the sorting criteria columns
    v''     <- C.project (TTupElem First TInput) v'

    l'      <- updateLayoutMaps (RMap r) xl

    return (dv { dvPhysVec = v''}, l')

--------------------------------------------------------------------------------
-- group

group :: UnVectMacro
group dv (LTuple [xl, gl]) = do
    (vo, vi, r) <- C.group (TTupElem (Next First) TInput) (dvPhysVec dv)
    vi'         <- C.project (TTupElem First TInput) vi
    xl'         <- updateLayoutMaps (RMap r) xl
    return (dv { dvPhysVec = vo }, LTuple [gl, LNest (DelayedVec IDMap vi') xl'])

--------------------------------------------------------------------------------
-- ext

ext :: L.ScalarVal -> UnVectMacro
ext val dv lyt = do
    v' <- C.project (TMkTuple [TInput, TConstant val]) (dvPhysVec dv)
    return (dv { dvPhysVec = v' }, LTuple [lyt, LCol])

--------------------------------------------------------------------------------
-- Filtering

restrict :: UnVectMacro
restrict dv (LTuple [l, LCol]) = do
    -- Filter the vector according to the boolean column
    (v, r) <- C.select (TTupElem (Next First) TInput) (dvPhysVec dv)
    v'     <- C.project (TTupElem First TInput) v
    l'     <- updateLayoutMaps (RMap r) l

    return (dv { dvPhysVec = v' }, l')

--------------------------------------------------------------------------------
-- Applying unary vectorization macros

unMacroL :: UnVectMacro -> Shape DelayedVec -> VSLBuild TExpr TExpr (Shape DelayedVec)
unMacroL macro (VShape dvo (LNest dvi l)) = VShape dvo <$> uncurry LNest <$> macro dvi l

--------------------------------------------------------------------------------
-- Binary Vectorization Macros

type BinVectMacro =    DelayedVec -> Layout DelayedVec
                    -> DelayedVec -> Layout DelayedVec
                    -> VSLBuild TExpr TExpr (DelayedVec, Layout DelayedVec)

--------------------------------------------------------------------------------
-- Applying binary vectorization macros

binMacroL :: BinVectMacro -> Shape DelayedVec -> Shape DelayedVec -> VSLBuild TExpr TExpr (Shape DelayedVec)
binMacroL macro (VShape dvo (LNest dvi1 l1)) (VShape _ (LNest dvi2 l2)) =
    VShape dvo <$> uncurry LNest <$> macro dvi1 l1 dvi2 l2


--------------------------------------------------------------------------------
-- Binary Vectorization Macros

append :: BinVectMacro
append dv1 l1 dv2 l2 = do
    (v1, l1')   <- materializeShape dv1 l1
    (v2, l2')   <- materializeShape dv2 l2
    (v, r1, r2) <- C.append v1 v2
    l1''        <- updateLayoutMaps (RMap r1) l1'
    l2''        <- updateLayoutMaps (RMap r2) l2'
    l           <- appendLayouts l1'' l2''
    return $ (MatVec v, l)

zip :: BinVectMacro
zip dv1 l1 dv2 l2 = do
    (v1, l1') <- materializeShape dv1 l1
    (v2, l2') <- materializeShape dv2 l2
    (v, r1, r2) <- C.zip v1 v2
    l1'' <- updateLayoutMaps (RMap r1) l1'
    l2'' <- updateLayoutMaps (RMap r2) l2'
    return (MatVec v, LTuple [l1'', l2''])


nestjoin :: L.JoinPredicate L.ScalarExpr -> BinVectMacro
nestjoin p dv1 l1 (DelayedVec m2 v2) l2 = do
    (v1, l1') <- materializeShape dv1 l1
    case m2 of
        IDMap -> do
            (v, r1, r2) <- C.nestjoinMM (scalarExpr <$> p) v1 v2
            vo          <- C.project (TMkTuple [TInput, TIndex]) v1
            l1'' <- updateLayoutMaps (RMap r1) l1'
            l2'  <- updateLayoutMaps (RMap r2) l2
            return ( DelayedVec IDMap vo
                   , LTuple [l1', LNest (DelayedVec IDMap v) (LTuple [l1'', l2'])])
        UnitMap _ -> do
            (v, r1, r2) <- C.nestjoinMU (scalarExpr <$> p) v1 v2
            vo          <- C.project (TMkTuple [TInput, TIndex]) v1
            l1'' <- updateLayoutMaps (RMap r1) l1'
            l2'  <- updateLayoutMaps (RMap r2) l2
            return ( DelayedVec IDMap vo
                   , LTuple [l1', LNest (DelayedVec IDMap v) (LTuple [l1'', l2'])])
        RMap m -> do
            (v2', l2') <- materializeShape (DelayedVec (RMap m) v2) l2
            (v, r1, r2) <- C.nestjoinMM (scalarExpr <$> p) v1 v2'
            vo          <- C.project (TMkTuple [TInput, TIndex]) v1
            l1'' <- updateLayoutMaps (RMap r1) l1'
            l2''  <- updateLayoutMaps (RMap r2) l2'
            return ( DelayedVec IDMap vo
                   , LTuple [l1', LNest (DelayedVec IDMap v) (LTuple [l1'', l2''])])

thetajoin :: L.JoinPredicate L.ScalarExpr -> BinVectMacro
thetajoin p dv1 l1 dv2 l2 =
    case (dvSegMap dv1, dvSegMap dv2) of
        (UnitMap m1, UnitMap _) -> do
            (v, r1, r2) <- C.thetajoinMM (scalarExpr <$> p) (dvPhysVec dv1) (dvPhysVec dv2)
            l1' <- updateLayoutMaps (RMap r1) l1
            l2' <- updateLayoutMaps (RMap r2) l2
            return (DelayedVec (UnitMap m1) v, LTuple [l1', l2'])
        (IDMap, UnitMap _) -> do
            (v, r1, r2) <- C.thetajoinMU (scalarExpr <$> p) (dvPhysVec dv1) (dvPhysVec dv2)
            l1' <- updateLayoutMaps (RMap r1) l1
            l2' <- updateLayoutMaps (RMap r2) l2
            return (DelayedVec IDMap v, LTuple [l1', l2'])
        (UnitMap _, IDMap) -> do
            (v, r1, r2) <- C.thetajoinUM (scalarExpr <$> p) (dvPhysVec dv1) (dvPhysVec dv2)
            l1' <- updateLayoutMaps (RMap r1) l1
            l2' <- updateLayoutMaps (RMap r2) l2
            return (DelayedVec IDMap v, LTuple [l1', l2'])
        _ -> do
            (v1', l1') <- materializeShape dv1 l1
            (v2', l2') <- materializeShape dv2 l2
            (v, r1, r2) <- C.thetajoinMM (scalarExpr <$> p) v1' v2'
            l1'' <- updateLayoutMaps (RMap r1) l1'
            l2'' <- updateLayoutMaps (RMap r2) l2'
            return (DelayedVec IDMap v, LTuple [l1'', l2''])

cartproduct :: BinVectMacro
cartproduct dv1 l1 dv2 l2 = do
    (v1', l1') <- materializeShape dv1 l1
    (v2', l2') <- materializeShape dv2 l2
    (v, r1, r2) <- C.cartproduct v1' v2'
    l1'' <- updateLayoutMaps (RMap r1) l1'
    l2'' <- updateLayoutMaps (RMap r2) l2'
    return (DelayedVec IDMap v, LTuple [l1'', l2''])

antijoin :: L.JoinPredicate L.ScalarExpr -> BinVectMacro
antijoin p dv1 l1 dv2 l2 =
    case (dvSegMap dv1, dvSegMap dv2) of
        (UnitMap m1, UnitMap _) -> do
            (v, r1) <- C.antijoinMM (scalarExpr <$> p) (dvPhysVec dv1) (dvPhysVec dv2)
            l1' <- updateLayoutMaps (RMap r1) l1
            return (DelayedVec (UnitMap m1) v, l1')
        (IDMap, UnitMap _) -> do
            (v, r1) <- C.antijoinMU (scalarExpr <$> p) (dvPhysVec dv1) (dvPhysVec dv2)
            l1' <- updateLayoutMaps (RMap r1) l1
            return (DelayedVec IDMap v, l1')
        (UnitMap _, IDMap) -> do
            (v, r1) <- C.antijoinUM (scalarExpr <$> p) (dvPhysVec dv1) (dvPhysVec dv2)
            l1' <- updateLayoutMaps (RMap r1) l1
            return (DelayedVec IDMap v, l1')
        _ -> do
            (v1', l1') <- materializeShape dv1 l1
            (v2', _) <- materializeShape dv2 l2
            (v, r1) <- C.antijoinMM (scalarExpr <$> p) v1' v2'
            l1'' <- updateLayoutMaps (RMap r1) l1'
            return (DelayedVec IDMap v, l1'')

semijoin :: L.JoinPredicate L.ScalarExpr -> BinVectMacro
semijoin p dv1 l1 dv2 l2 =
    case (dvSegMap dv1, dvSegMap dv2) of
        (UnitMap m1, UnitMap _) -> do
            (v, r1) <- C.semijoinMM (scalarExpr <$> p) (dvPhysVec dv1) (dvPhysVec dv2)
            l1' <- updateLayoutMaps (RMap r1) l1
            return (DelayedVec (UnitMap m1) v, l1')
        (IDMap, UnitMap _) -> do
            (v, r1) <- C.semijoinMU (scalarExpr <$> p) (dvPhysVec dv1) (dvPhysVec dv2)
            l1' <- updateLayoutMaps (RMap r1) l1
            return (DelayedVec IDMap v, l1')
        (UnitMap _, IDMap) -> do
            (v, r1) <- C.semijoinUM (scalarExpr <$> p) (dvPhysVec dv1) (dvPhysVec dv2)
            l1' <- updateLayoutMaps (RMap r1) l1
            return (DelayedVec IDMap v, l1')
        _ -> do
            (v1', l1') <- materializeShape dv1 l1
            (v2', _) <- materializeShape dv2 l2
            (v, r1) <- C.semijoinMM (scalarExpr <$> p) v1' v2'
            l1'' <- updateLayoutMaps (RMap r1) l1'
            return (DelayedVec IDMap v, l1'')

groupjoin :: L.JoinPredicate L.ScalarExpr -> L.NE (AggrFun TExpr) -> BinVectMacro
groupjoin p as dv1 l1 dv2 l2 =
    case (dvSegMap dv1, dvSegMap dv2) of
        (UnitMap m1, UnitMap _) -> do
            v <- C.groupjoinMM (scalarExpr <$> p) as (dvPhysVec dv1) (dvPhysVec dv2)
            return (DelayedVec (UnitMap m1) v, mkLyt l1)
        (IDMap, UnitMap _) -> do
            v <- C.groupjoinMU (scalarExpr <$> p) as (dvPhysVec dv1) (dvPhysVec dv2)
            return (DelayedVec IDMap v, mkLyt l1)
        (UnitMap _, IDMap) -> do
            v <- C.groupjoinUM (scalarExpr <$> p) as (dvPhysVec dv1) (dvPhysVec dv2)
            return (DelayedVec IDMap v, mkLyt l1)
        _ -> do
            (v1', l1') <- materializeShape dv1 l1
            (v2', _) <- materializeShape dv2 l2
            v <- C.groupjoinMM (scalarExpr <$> p) as v1' v2'
            return (DelayedVec IDMap v, mkLyt l1')
  where
    mkLyt leftLyt = LTuple $ leftLyt : map (const LCol) (N.toList $ L.getNE as)

--------------------------------------------------------------------------------
-- Ternary Vectorization Macros

type TerVectMacro =    DelayedVec -> Layout DelayedVec
                    -> DelayedVec -> Layout DelayedVec
                    -> DelayedVec -> Layout DelayedVec
                    -> VSLBuild TExpr TExpr (DelayedVec, Layout DelayedVec)

terMacroL :: TerVectMacro
          -> Shape DelayedVec
          -> Shape DelayedVec
          -> Shape DelayedVec
          -> VSLBuild TExpr TExpr (Shape DelayedVec)
terMacroL macro (VShape dvo (LNest dvi1 l1)) (VShape _ (LNest dvi2 l2)) (VShape _ (LNest dvi3 l3)) =
    VShape dvo <$> uncurry LNest <$> macro dvi1 l1 dvi2 l2 dvi3 l3

--------------------------------------------------------------------------------
-- Conditionals

combine :: TerVectMacro
combine dvb LCol dv1 l1 dv2 l2 = do
    (vb, _)     <- materializeShape dvb LCol
    (v1, l1')   <- materializeShape dv1 l1
    (v2, l2')   <- materializeShape dv2 l2
    (v, r1, r2) <- C.combine vb v1 v2
    l1''        <- updateLayoutMaps (RMap r1) l1'
    l2''        <- updateLayoutMaps (RMap r2) l2'
    l           <- appendLayouts l1'' l2''
    return (MatVec v, l)

--------------------------------------------------------------------------------
-- Distribution/Replication

dist :: Shape DelayedVec -> Shape DelayedVec -> VSLBuild TExpr TExpr (Shape DelayedVec)
dist (VShape (DelayedVec IDMap v1) l1) (VShape dv2 _) = do
    outerVec <- C.project TIndex (dvPhysVec dv2)
    innerMap <- UnitMap <$> C.unitmap (dvPhysVec dv2)
    return $ VShape (dv2 { dvPhysVec = outerVec }) (LNest (DelayedVec innerMap v1) l1)
dist _ _ = error "VSL.Vectorize.dist"

distL :: Shape DelayedVec -> Shape DelayedVec -> VSLBuild TExpr TExpr (Shape DelayedVec)
distL (VShape dv1 l1) (VShape dvo (LNest dv2 l2)) = do
    (v1, l1') <- materializeShape dv1 l1
    (v2, l2') <- materializeShape dv2 l2
    (v, r)    <- C.replicateseg v1 v2
    l1''      <- updateLayoutMaps (RMap r) l1'

    -- Keep only payload columns from the left (outer vector)
    let l = LTuple [l1'', l2']
    VShape dv' lf <- tupElemL First $ VShape (MatVec v) l

    return $ VShape dvo (LNest dv' lf)

--------------------------------------------------------------------------------

materializeShape :: DelayedVec -> Layout DelayedVec -> VSLBuild TExpr TExpr (DVec, Layout DelayedVec)
materializeShape (DelayedVec sm v) l =
    case sm of
        IDMap -> return (v, l)
        UnitMap m -> do
            (v', r) <- C.materialize m v
            l'      <- updateLayoutMaps (RMap r) l
            return (v', l')
        RMap m -> do
            (v', r) <- C.materialize m v
            l'      <- updateLayoutMaps (RMap r) l
            return (v', l')


updateLayoutMaps :: SegMap -> Layout DelayedVec -> VSLBuild TExpr TExpr (Layout DelayedVec)
updateLayoutMaps newMap = go
  where
    updateDelayedVec (DelayedVec oldMap v) = DelayedVec <$> updateSegMap newMap oldMap <*> pure v

    go (LNest dv lyt) = LNest <$> updateDelayedVec dv <*> pure lyt
    go (LTuple lyts)  = LTuple <$> traverse (updateLayoutMaps newMap) lyts
    go LCol           = pure LCol

updateSegMap :: SegMap -> SegMap -> VSLBuild TExpr TExpr SegMap
updateSegMap (RMap mapUpdate) (RMap oldMap) = RMap <$> C.updatemap mapUpdate oldMap
updateSegMap (RMap mapUpdate) (UnitMap _)   = UnitMap <$> C.updateunit mapUpdate
updateSegMap (RMap mapUpdate) IDMap         = pure $ RMap mapUpdate
updateSegMap _ _ = error "updateSegMap"

appendLayouts :: Layout DelayedVec -> Layout DelayedVec -> VSLBuild TExpr TExpr (Layout DelayedVec)
appendLayouts LCol LCol = return LCol
appendLayouts (LNest dv1 l1) (LNest dv2 l2) = do
    (v1, l1')   <- materializeShape dv1 l1
    (v2, l2')   <- materializeShape dv2 l2
    (v, r1, r2) <- C.append v1 v2
    l1''        <- updateLayoutMaps (RMap r1) l1'
    l2''        <- updateLayoutMaps (RMap r2) l2'
    l           <- appendLayouts l1'' l2''
    return $ LNest (MatVec v) l
appendLayouts (LTuple ls1) (LTuple ls2) =
    LTuple <$> zipWithM appendLayouts ls1 ls2

--------------------------------------------------------------------------------
-- Construction of base tables and literal tables

-- | Create a SL reference to a base table.
dbTable :: String -> L.BaseTableSchema -> VSLBuild TExpr TExpr (Shape DelayedVec)
dbTable n schema = do
    tab <- C.tableref n schema
    -- Single-column tables are represented by a flat list and map to
    -- a flat one-column layout. Multi-column tables map to a list of
    -- tuples and the corresponding tuple layout.
    let lyt = case L.tableCols schema of
                  _ N.:| [] -> LCol
                  cs        -> LTuple $ map (const LCol) $ N.toList cs
    return $ VShape (DelayedVec IDMap tab) lyt

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

shredType :: T.Type -> Layout (PType, S.Seq SegD)
shredType (T.ScalarT _) = LCol
shredType (T.TupleT ts) = LTuple $ map shredType ts
shredType (T.ListT t)   = LNest (payloadType t, S.empty) (shredType t)

payloadType :: T.Type -> PType
payloadType (T.ScalarT t) = PScalarT t
payloadType (T.TupleT ts) = PTupleT (N.fromList $ map payloadType ts)
payloadType (T.ListT _)   = PIndexT

literalVectors :: Layout (PType, S.Seq SegD) -> VSLBuild TExpr TExpr (Layout DelayedVec)
literalVectors lyt = traverse go lyt
  where
    go (ty, segs) = DelayedVec IDMap <$> C.lit (ty, Segs segs)

literalShape :: Shape (PType, S.Seq SegD) -> VSLBuild TExpr TExpr (Shape DelayedVec)
literalShape (VShape (ty, segs) lyt) = do
    let seg = if S.null segs then $impossible else S.index segs 0
    shapeVec <- C.lit (ty, UnitSeg seg)
    vecLyt   <- literalVectors lyt
    return $ VShape (DelayedVec IDMap shapeVec) vecLyt

shredLiteral :: T.Type -> L.Val -> VSLBuild TExpr TExpr (Shape DelayedVec)
shredLiteral (T.ListT t) (L.ListV vs) = literalShape $ VShape (payloadType t, S.singleton seg) lyt
  where
    initLyt    = shredType t
    (seg, lyt) = shredList vs initLyt
shredLiteral _ _ = $impossible
