{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}

{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

module Database.DSH.VSL.Builtins where

import           Control.Monad
import qualified Data.List                      as List
import qualified Data.List.NonEmpty             as N
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

pattern MatVec v = DelayedVec IDMap v

--------------------------------------------------------------------------------
-- Unary scalar operators

unOp :: L.ScalarUnOp -> Shape DelayedVec -> VSLBuild (Shape DelayedVec)
unOp o (SShape (MatVec v) LCol) = do
    vp <- C.project [UnApp o (Column 1)] v
    return $ SShape (MatVec vp) LCol

unOpL :: L.ScalarUnOp -> Shape DelayedVec -> VSLBuild (Shape DelayedVec)
unOpL o (VShape (DelayedVec m v) LCol) = do
    vp <- C.project [UnApp o (Column 1)] v
    return $ VShape (DelayedVec m vp) LCol

--------------------------------------------------------------------------------
-- Binary scalar operators

binOp :: L.ScalarBinOp -> Shape DelayedVec -> Shape DelayedVec -> VSLBuild (Shape DelayedVec)
binOp o (SShape (MatVec v1) LCol) (SShape (MatVec v2) LCol) = do
    (v, _, _) <- C.cartproduct v1 v2
    v'        <- C.project [BinApp o (Column 1) (Column 2)] v
    return $ SShape (DelayedVec IDMap v') LCol
binOp _ _ _ = error "VSL.Vectorize.binOp"

binOpL :: L.ScalarBinOp -> Shape DelayedVec -> Shape DelayedVec -> VSLBuild (Shape DelayedVec)
binOpL o (VShape dv1 LCol) (VShape dv2 LCol) = do
    case (dvSegMap dv1, dvSegMap dv2) of
        (RMap m1, RMap _) -> do
            v  <- C.align (dvPhysVec dv1) (dvPhysVec dv2)
            v' <- C.project [BinApp o (Column 1) (Column 2)] v
            return $ VShape (DelayedVec (RMap m1) v') LCol
        (UnitMap m1, UnitMap _) -> do
            v  <- C.align (dvPhysVec dv1) (dvPhysVec dv2)
            v' <- C.project [BinApp o (Column 1) (Column 2)] v
            return $ VShape (DelayedVec (UnitMap m1) v') LCol
        (IDMap, IDMap) -> do
            v  <- C.align (dvPhysVec dv1) (dvPhysVec dv2)
            v' <- C.project [BinApp o (Column 1) (Column 2)] v
            return $ VShape (DelayedVec IDMap v') LCol
        (RMap m1, IDMap) -> do
            -- Materialize the left input
            -- We do not need the replication vector because the layout is flat
            (mv1, _) <- C.materialize m1 (dvPhysVec dv1)
            v        <- C.align mv1 (dvPhysVec dv2)
            v'       <- C.project [BinApp o (Column 1) (Column 2)] v
            return $ VShape (DelayedVec IDMap v') LCol
        (IDMap, RMap m2) -> do
            -- Materialize the right input
            -- We do not need the replication vector because the layout is flat
            (mv2, _) <- C.materialize m2 (dvPhysVec dv2)
            v        <- C.align (dvPhysVec dv1) mv2
            v'       <- C.project [BinApp o (Column 1) (Column 2)] v
            return $ VShape (DelayedVec IDMap v') LCol

--------------------------------------------------------------------------------
-- Tuple indexing

tupElem :: TupleIndex -> Shape DelayedVec -> VSLBuild (Shape DelayedVec)
tupElem i (SShape (MatVec v) (LTuple ls)) =
    case ls !! (tupleIndex i - 1) of
        LNest dv l -> do
            (vi, li) <- materializeShape dv l
            vi'      <- C.unsegment vi
            return $ VShape (DelayedVec IDMap vi') li
        _          -> do
            let (l, cols) = projectColumns i ls
            vp <- C.project (map Column cols) v
            return $ SShape (DelayedVec IDMap vp) l

tupElemL :: TupleIndex -> Shape DelayedVec -> VSLBuild (Shape DelayedVec)
tupElemL i (VShape dv (LTuple ls)) = do
    let (l, cols) = projectColumns i ls
    vp <- C.project (map Column cols) (dvPhysVec dv)
    return $ VShape (dv { dvPhysVec = vp }) (l)

--------------------------------------------------------------------------------
-- Singleton list construction

sng :: Shape DelayedVec -> VSLBuild (Shape DelayedVec)
sng (VShape (MatVec v) l) = do
    (vo, vi) <- C.nest v
    return $ VShape (MatVec vo) (LNest (MatVec vi) l)
sng (SShape (MatVec v) l) = return $ VShape (MatVec v) l

sngL :: Shape DelayedVec -> VSLBuild (Shape DelayedVec)
sngL (VShape (DelayedVec m v) l) = do
    vo <- C.project [] v
    vi <- C.segment v
    return $ VShape (DelayedVec m vo) (LNest (DelayedVec IDMap vi) l)

--------------------------------------------------------------------------------
-- Aggregation

aggr :: (Expr -> AggrFun) -> Shape DelayedVec -> VSLBuild (Shape DelayedVec)
aggr afun (VShape (MatVec v) LCol) = do
    va <- C.aggr (afun (Column 1)) v
    return $ SShape (MatVec va) LCol

aggrL :: (Expr -> AggrFun) -> Shape DelayedVec -> VSLBuild (Shape DelayedVec)
aggrL afun (VShape dvo (LNest dvi LCol)) = do
    let a = afun (Column 1)
    -- Aggregate the physical segments without considering the segment map.
    va      <- C.aggrseg a (dvPhysVec dvi)
    -- To unbox, we need to materialize the inner vector. Crucially, we
    -- materialize *after* aggregation.
    (vm, _) <- materializeShape (dvi { dvPhysVec = va }) LCol
    vu      <- fst <$> defaultUnboxOp a (dvPhysVec dvo) vm
    return $ VShape (dvo { dvPhysVec = vu }) LCol

defaultUnboxOp :: AggrFun -> DVec -> DVec -> VSLBuild (DVec, RVec)
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

concat :: Shape DelayedVec -> VSLBuild (Shape DelayedVec)
concat (VShape _ (LNest dv l)) = do
    (v, l') <- materializeShape dv l
    v'      <- C.unsegment v
    return $ VShape (MatVec v') l'

concatL :: Shape DelayedVec -> VSLBuild (Shape DelayedVec)
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

tuple :: [Shape DelayedVec] -> VSLBuild (Shape DelayedVec)
tuple shapes = do
    (dv, ls) <- boxVectors shapes
    return $ SShape dv (LTuple ls)

-- | Align a list of shapes and nest vectors if necessary. This helper
-- function covers tuple construction in the unlifted case.
boxVectors :: [Shape DelayedVec] -> VSLBuild (DelayedVec, [Layout DelayedVec])
boxVectors [SShape dv l]              = do
    (v, l') <- materializeShape dv l
    return (MatVec v, [l'])
boxVectors [VShape dv l]              = do
    (v, l') <- materializeShape dv l
    (vo, vi) <- C.nest v
    return (MatVec vo, [LNest (MatVec vi) l'])
boxVectors (SShape dv l : shapes) = do
    (v, l') <- materializeShape dv l
    (dvb, ls)      <- boxVectors shapes
    (vb', r1, r2) <- C.cartproduct v (dvPhysVec dvb)
    l''             <- updateLayoutMaps (RMap r1) l'
    ls'            <- mapM (updateLayoutMaps (RMap r2)) ls
    return (MatVec vb', l'' : ls')
boxVectors (VShape dv l : shapes) = do
    (dvb, ls)      <- boxVectors shapes
    (v, l') <- materializeShape dv l
    (vo, vi)      <- C.nest v
    (vb', r1, r2) <- C.cartproduct vo (dvPhysVec dvb)
    l''           <- updateLayoutMaps (RMap r1) (LNest (MatVec vi) l')
    ls'           <- mapM (updateLayoutMaps (RMap r2)) ls
    return (MatVec vb', l'' : ls')
boxVectors s = error $ show s

tupleL :: [Shape DelayedVec] -> VSLBuild (Shape DelayedVec)
tupleL shapes =
    case shapes of
        (VShape (DelayedVec (UnitMap m) v) l) : shs
            | all isUnitShape shs -> do
          let (vs, ls) = unzip $ map (\(VShape (DelayedVec _ v') l') -> (v', l')) shs
          va <- alignVectors $ v : vs
          return $ VShape (DelayedVec (UnitMap m) va) (LTuple $ l:ls)
        _ -> do
          (vs, ls) <- unzip <$> mapM (\(VShape dv l) -> materializeShape dv l) shapes
          v        <- alignVectors vs
          return $ VShape (MatVec v) (LTuple ls)

alignVectors :: [DVec] -> VSLBuild DVec
alignVectors [v] = return v
alignVectors (v:vs) = do
    vsa <- alignVectors vs
    C.align v vsa

isUnitShape :: Shape DelayedVec -> Bool
isUnitShape (VShape (DelayedVec (UnitMap _) _) _) = True
isUnitShape _                                     = False

--------------------------------------------------------------------------------
-- Singleton list conversion

only :: Shape DelayedVec -> VSLBuild (Shape DelayedVec)
only (VShape _ (LNest dv l)) = do
    (v, l') <- materializeShape dv l
    v' <- C.unsegment v
    return $ VShape (MatVec v') l'
only (VShape (MatVec v) l) = SShape <$> (MatVec <$> C.unsegment v) <*> pure l

onlyL :: Shape DelayedVec -> VSLBuild (Shape DelayedVec)
onlyL (VShape dvo (LNest dvi li)) = do
    (vim, lim) <- materializeShape dvi li
    (vu, r) <- C.unboxsng (dvPhysVec dvo) vim
    lim' <- updateLayoutMaps (RMap r) lim
    return $ VShape (dvo { dvPhysVec = vu }) lim'

--------------------------------------------------------------------------------
-- Unary vectorization macros

type UnVectMacro = DelayedVec -> Layout DelayedVec -> VSLBuild (DelayedVec, Layout DelayedVec)

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
sort dv (LTuple [xl, sl]) = do
    let leftWidth  = columnsInLayout xl
        rightWidth = columnsInLayout sl

        sortExprs = map Column [leftWidth+1..leftWidth+rightWidth]

    -- Sort by all sorting columns from the right tuple component
    (v', r) <- C.sort sortExprs (dvPhysVec dv)
    -- After sorting, discard the sorting criteria columns
    v''     <- C.project (map Column [1..leftWidth]) v'

    l'      <- updateLayoutMaps (RMap r) xl

    return (dv { dvPhysVec = v''}, l')

--------------------------------------------------------------------------------
-- group

group :: UnVectMacro
group dv (LTuple [xl, gl]) = do
    let leftWidth  = columnsInLayout xl
        rightWidth = columnsInLayout gl

        groupExprs = map Column [leftWidth+1..leftWidth+rightWidth]

    (vo, vi, r) <- C.group groupExprs (dvPhysVec dv)
    vi'         <- C.project (map Column [1..leftWidth]) vi
    xl'         <- updateLayoutMaps (RMap r) xl
    return (dv { dvPhysVec = vo }, LTuple [gl, LNest (DelayedVec IDMap vi') xl'])

--------------------------------------------------------------------------------
-- Filtering

restrict :: UnVectMacro
restrict dv (LTuple [l, LCol]) = do
    -- The right input vector has only one boolean column which
    -- defines wether the tuple at the same position in the left input
    -- is preserved.
    let leftWidth = columnsInLayout l
        predicate = Column $ leftWidth + 1

    -- Filter the vector according to the boolean column
    (v, r) <- C.select predicate (dvPhysVec dv)
    v'     <- C.project (map Column [1..leftWidth]) v
    l'     <- updateLayoutMaps (RMap r) l

    return (dv { dvPhysVec = v' }, l')

--------------------------------------------------------------------------------
-- Applying unary vectorization macros

unMacro :: UnVectMacro -> Shape DelayedVec -> VSLBuild (Shape DelayedVec)
unMacro macro (VShape dv l) = uncurry VShape <$> macro dv l

unMacroL :: UnVectMacro -> Shape DelayedVec -> VSLBuild (Shape DelayedVec)
unMacroL macro (VShape dvo (LNest dvi l)) = VShape dvo <$> uncurry LNest <$> macro dvi l

--------------------------------------------------------------------------------
-- Binary Vectorization Macros

type BinVectMacro =    DelayedVec -> Layout DelayedVec
                    -> DelayedVec -> Layout DelayedVec
                    -> VSLBuild (DelayedVec, Layout DelayedVec)

--------------------------------------------------------------------------------
-- Applying binary vectorization macros

binMacro :: BinVectMacro -> Shape DelayedVec -> Shape DelayedVec -> VSLBuild (Shape DelayedVec)
binMacro macro (VShape dv1 l1) (VShape dv2 l2) = uncurry VShape <$> macro dv1 l1 dv2 l2

binMacroL :: BinVectMacro -> Shape DelayedVec -> Shape DelayedVec -> VSLBuild (Shape DelayedVec)
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
            (v, r1, r2) <- C.nestjoinMM p v1 v2
            l1'' <- updateLayoutMaps (RMap r1) l1'
            l2'  <- updateLayoutMaps (RMap r2) l2
            return ( DelayedVec IDMap v1
                   , LTuple [l1', LNest (DelayedVec IDMap v) (LTuple [l1'', l2'])])
        UnitMap _ -> do
            (v, r1, r2) <- C.nestjoinMU p v1 v2
            l1'' <- updateLayoutMaps (RMap r1) l1'
            l2'  <- updateLayoutMaps (RMap r2) l2
            return ( DelayedVec IDMap v1
                   , LTuple [l1', LNest (DelayedVec IDMap v) (LTuple [l1'', l2'])])
        RMap m -> do
            (v2', l2') <- materializeShape (DelayedVec (RMap m) v2) l2
            (v, r1, r2) <- C.nestjoinMM p v1 v2'
            l1'' <- updateLayoutMaps (RMap r1) l1'
            l2''  <- updateLayoutMaps (RMap r2) l2'
            return ( DelayedVec IDMap v1
                   , LTuple [l1', LNest (DelayedVec IDMap v) (LTuple [l1'', l2''])])

thetajoin :: L.JoinPredicate L.ScalarExpr -> BinVectMacro
thetajoin p dv1 l1 dv2 l2 =
    case (dvSegMap dv1, dvSegMap dv2) of
        (UnitMap m1, UnitMap _) -> do
            (v, r1, r2) <- C.thetajoinMM p (dvPhysVec dv1) (dvPhysVec dv2)
            l1' <- updateLayoutMaps (RMap r1) l1
            l2' <- updateLayoutMaps (RMap r2) l2
            return (DelayedVec (UnitMap m1) v, LTuple [l1', l2'])
        (IDMap, UnitMap _) -> do
            (v, r1, r2) <- C.thetajoinMU p (dvPhysVec dv1) (dvPhysVec dv2)
            l1' <- updateLayoutMaps (RMap r1) l1
            l2' <- updateLayoutMaps (RMap r2) l2
            return (DelayedVec IDMap v, LTuple [l1', l2'])
        (UnitMap _, IDMap) -> do
            (v, r1, r2) <- C.thetajoinUM p (dvPhysVec dv1) (dvPhysVec dv2)
            l1' <- updateLayoutMaps (RMap r1) l1
            l2' <- updateLayoutMaps (RMap r2) l2
            return (DelayedVec IDMap v, LTuple [l1', l2'])
        _ -> do
            (v1', l1') <- materializeShape dv1 l1
            (v2', l2') <- materializeShape dv2 l2
            (v, r1, r2) <- C.thetajoinMM p v1' v2'
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
            (v, r1) <- C.antijoinMM p (dvPhysVec dv1) (dvPhysVec dv2)
            l1' <- updateLayoutMaps (RMap r1) l1
            return (DelayedVec (UnitMap m1) v, l1')
        (IDMap, UnitMap _) -> do
            (v, r1) <- C.antijoinMU p (dvPhysVec dv1) (dvPhysVec dv2)
            l1' <- updateLayoutMaps (RMap r1) l1
            return (DelayedVec IDMap v, l1')
        (UnitMap _, IDMap) -> do
            (v, r1) <- C.antijoinUM p (dvPhysVec dv1) (dvPhysVec dv2)
            l1' <- updateLayoutMaps (RMap r1) l1
            return (DelayedVec IDMap v, l1')
        _ -> do
            (v1', l1') <- materializeShape dv1 l1
            (v2', _) <- materializeShape dv2 l2
            (v, r1) <- C.antijoinMM p v1' v2'
            l1'' <- updateLayoutMaps (RMap r1) l1'
            return (DelayedVec IDMap v, l1'')

semijoin :: L.JoinPredicate L.ScalarExpr -> BinVectMacro
semijoin p dv1 l1 dv2 l2 =
    case (dvSegMap dv1, dvSegMap dv2) of
        (UnitMap m1, UnitMap _) -> do
            (v, r1) <- C.semijoinMM p (dvPhysVec dv1) (dvPhysVec dv2)
            l1' <- updateLayoutMaps (RMap r1) l1
            return (DelayedVec (UnitMap m1) v, l1')
        (IDMap, UnitMap _) -> do
            (v, r1) <- C.semijoinMU p (dvPhysVec dv1) (dvPhysVec dv2)
            l1' <- updateLayoutMaps (RMap r1) l1
            return (DelayedVec IDMap v, l1')
        (UnitMap _, IDMap) -> do
            (v, r1) <- C.semijoinUM p (dvPhysVec dv1) (dvPhysVec dv2)
            l1' <- updateLayoutMaps (RMap r1) l1
            return (DelayedVec IDMap v, l1')
        _ -> do
            (v1', l1') <- materializeShape dv1 l1
            (v2', _) <- materializeShape dv2 l2
            (v, r1) <- C.semijoinMM p v1' v2'
            l1'' <- updateLayoutMaps (RMap r1) l1'
            return (DelayedVec IDMap v, l1'')

groupjoin :: L.JoinPredicate L.ScalarExpr -> L.NE AggrFun -> BinVectMacro
groupjoin p as dv1 l1 dv2 l2 =
    case (dvSegMap dv1, dvSegMap dv2) of
        (UnitMap m1, UnitMap _) -> do
            v <- C.groupjoinMM p as (dvPhysVec dv1) (dvPhysVec dv2)
            return (DelayedVec (UnitMap m1) v, mkLyt l1)
        (IDMap, UnitMap _) -> do
            v <- C.groupjoinMU p as (dvPhysVec dv1) (dvPhysVec dv2)
            return (DelayedVec IDMap v, mkLyt l1)
        (UnitMap _, IDMap) -> do
            v <- C.groupjoinUM p as (dvPhysVec dv1) (dvPhysVec dv2)
            return (DelayedVec IDMap v, mkLyt l1)
        _ -> do
            (v1', l1') <- materializeShape dv1 l1
            (v2', _) <- materializeShape dv2 l2
            v <- C.groupjoinMM p as v1' v2'
            return (DelayedVec IDMap v, mkLyt l1')
  where
    mkLyt leftLyt = LTuple $ leftLyt : map (const LCol) (N.toList $ L.getNE as)

--------------------------------------------------------------------------------
-- Ternary Vectorization Macros

type TerVectMacro =    DelayedVec -> Layout DelayedVec
                    -> DelayedVec -> Layout DelayedVec
                    -> DelayedVec -> Layout DelayedVec
                    -> VSLBuild (DelayedVec, Layout DelayedVec)

terMacro :: TerVectMacro
         -> Shape DelayedVec
         -> Shape DelayedVec
         -> Shape DelayedVec
         -> VSLBuild (Shape DelayedVec)
terMacro macro (VShape dv1 l1) (VShape dv2 l2) (VShape dv3 l3) =
    uncurry VShape <$> macro dv1 l1 dv2 l2 dv3 l3

terMacroL :: TerVectMacro
          -> Shape DelayedVec
          -> Shape DelayedVec
          -> Shape DelayedVec
          -> VSLBuild (Shape DelayedVec)
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

if_ :: Shape DelayedVec -> Shape DelayedVec -> Shape DelayedVec -> VSLBuild (Shape DelayedVec)
if_ (SShape dvb LCol) (VShape dv1 l1) (VShape dv2 l2) = do
    (thenVec, thenLyt) <- branchVec id (SShape dvb LCol) (VShape dv1 l1)
    (elseVec, elseLyt) <- branchVec (UnApp (L.SUBoolOp L.Not)) (SShape dvb LCol) (VShape dv2 l2)
    lyt                <- appendLayouts thenLyt elseLyt
    (ifVec, _, _)      <- C.append thenVec elseVec
    return $ VShape (MatVec ifVec) lyt
if_ (SShape dvb LCol) (SShape dv1 l1) (SShape dv2 l2) = do
    (thenVec, thenLyt) <- branchVec id (SShape dvb LCol) (VShape dv1 l1)
    (elseVec, elseLyt) <- branchVec (UnApp (L.SUBoolOp L.Not)) (SShape dvb LCol) (VShape dv2 l2)
    lyt                <- appendLayouts thenLyt elseLyt
    (ifVec, _, _)      <- C.append thenVec elseVec
    return $ SShape (MatVec ifVec) lyt

branchVec :: (Expr -> Expr)
          -> Shape DelayedVec
          -> Shape DelayedVec
          -> VSLBuild (DVec, Layout DelayedVec)
branchVec p (SShape dvb LCol) (VShape dv1 l1) = do
    let leftWidth = columnsInLayout l1
    VShape (MatVec v) _ <- dist (SShape dvb LCol) (VShape dv1 l1)
    (v', r)             <- C.select (p $ Column 1) v
    vp                  <- C.project [ Column c | c <- [2..leftWidth+1] ] v'
    l1'                 <- updateLayoutMaps (RMap r) l1
    return (vp, l1')

--------------------------------------------------------------------------------
-- Distribution/Replication

dist :: Shape DelayedVec -> Shape DelayedVec -> VSLBuild (Shape DelayedVec)
dist (SShape dv1 l1) (VShape dv2 _) = do
    let leftWidth  = columnsInLayout l1
        proj       = map Column [1..leftWidth]
    (v, r)   <- C.replicatescalar (dvPhysVec dv1) (dvPhysVec dv2)
    outerVec <- C.project proj v
    innerLyt <- updateLayoutMaps (RMap r) l1
    return $ VShape (dv2 { dvPhysVec = outerVec }) innerLyt
dist (VShape (DelayedVec IDMap v1) l1) (VShape dv2 _) = do
    outerVec <- C.project [] (dvPhysVec dv2)
    innerMap <- UnitMap <$> C.unitmap (dvPhysVec dv2)
    return $ VShape (dv2 { dvPhysVec = outerVec }) (LNest (DelayedVec innerMap v1) l1)
dist _ _ = error "VSL.Vectorize.dist"

distL :: Shape DelayedVec -> Shape DelayedVec -> VSLBuild (Shape DelayedVec)
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

materializeShape :: DelayedVec -> Layout DelayedVec -> VSLBuild (DVec, Layout DelayedVec)
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


updateLayoutMaps :: SegMap -> Layout DelayedVec -> VSLBuild (Layout DelayedVec)
updateLayoutMaps newMap = go
  where
    updateDelayedVec (DelayedVec oldMap v) = DelayedVec <$> updateSegMap newMap oldMap <*> pure v

    go (LNest dv lyt) = LNest <$> updateDelayedVec dv <*> pure lyt
    go (LTuple lyts)  = LTuple <$> traverse (updateLayoutMaps newMap) lyts
    go LCol           = pure LCol

updateSegMap :: SegMap -> SegMap -> VSLBuild SegMap
updateSegMap (RMap mapUpdate) (RMap oldMap) = RMap <$> C.updatemap mapUpdate oldMap
updateSegMap (RMap mapUpdate) (UnitMap _)   = UnitMap <$> C.updateunit mapUpdate
updateSegMap (RMap mapUpdate) IDMap         = pure $ RMap mapUpdate
updateSegMap _ _ = error "updateSegMap"

appendLayouts :: Layout DelayedVec -> Layout DelayedVec -> VSLBuild (Layout DelayedVec)
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
dbTable :: String -> L.BaseTableSchema -> VSLBuild (Shape DelayedVec)
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
toColumns :: T.Type -> [L.Val] -> VSLBuild ([T.ScalarType], [Column], Layout DelayedVec)
toColumns (T.ListT t) ls    = do
    (v, lyt) <- toVector t ls
    return ([], [], LNest v lyt)
toColumns (T.TupleT tys) ts = do
    let tupleComponents = if null ts
                          then map (const []) tys
                          else List.transpose $ map fromTuple ts
    (colTys, cols, lyts) <- unzip3 <$> zipWithM toColumns tys tupleComponents
    return (List.concat colTys, List.concat cols, LTuple lyts)
toColumns (T.ScalarT t) vs  = return ([t], [S.fromList $ map scalarVal vs], LCol)

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
toVector :: T.Type -> [L.Val] -> VSLBuild (DelayedVec, Layout DelayedVec)
toVector t ls = do
    -- Concatenate the elements of all inner lists
    let innerLists = map fromList ls
        allElems   = List.concat innerLists
        innerLens  = map length innerLists
    (tys, cols, lyt) <- toColumns t allElems
    let segs = chopSegments innerLens cols
    litNode <- MatVec <$> C.lit (tys, SegFrame $ length allElems, Segs segs)
    return (litNode, lyt)

-- | Shred a literal value into flat vectors.
shredLiteral :: T.Type -> L.Val -> VSLBuild (Shape DelayedVec)
shredLiteral (T.ScalarT t) v = do
    (_, cols, _) <- toColumns (T.ScalarT t) [v]
    litNode <- MatVec <$> C.lit ([t], SegFrame 1, UnitSeg cols)
    return $ SShape litNode LCol
shredLiteral (T.TupleT t)  v  = do
    (tys, cols, lyt) <- toColumns (T.TupleT t) [v]
    litNode <- MatVec <$> C.lit (tys, SegFrame 1, UnitSeg cols)
    return $ SShape litNode lyt
shredLiteral (T.ListT t) (L.ListV es) = do
    (tys, cols, lyt) <- toColumns t es
    litNode <- MatVec <$> C.lit (tys, SegFrame $ length es, UnitSeg cols)
    return $ VShape litNode lyt
shredLiteral _ _ = $impossible
