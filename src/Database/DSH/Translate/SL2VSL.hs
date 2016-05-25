module Database.DSH.Translate.SL2VSL
    ( virtualizePlan
    ) where

import           Control.Monad.Reader
import           Control.Monad.State
import qualified Data.Foldable               as F
import qualified Data.IntMap                 as IM
import           Data.List.NonEmpty          (NonEmpty ((:|)))
import           Text.Printf

import qualified Database.Algebra.Dag        as D
import qualified Database.Algebra.Dag.Build  as B
import           Database.Algebra.Dag.Common

import           Database.DSH.Common.QueryPlan
import           Database.DSH.Common.Vector
import           Database.DSH.SL.Lang        (SL)
import qualified Database.DSH.SL.Lang        as SL
import           Database.DSH.VSL.Lang       (VSL)
import qualified Database.DSH.VSL.Lang       as VSL

type Cache = IM.IntMap Res

-- | A layer on top of the DAG builder monad that caches the translation result
-- of SL nodes and provides the environment of SL nodes.
type VecBuild = ReaderT (NodeMap SL) (StateT Cache (B.Build VSL))

runVecBuild :: NodeMap SL -> VecBuild Res -> (D.AlgebraDag VSL, Res)
runVecBuild slMap c = (dag, res)
  where
    (dag, res, _) = B.runBuild $ evalStateT (runReaderT c slMap) IM.empty

--------------------------------------------------------------------------------

virtualizePlan :: NodeMap SL -> Shape SLDVec -> VecBuild (Shape SLDVec)
virtualizePlan slMap shape = undefined $ runVecBuild slMap (virtualize undefined)

--------------------------------------------------------------------------------

data Res = Vec Vector
         | VecPair Vector Vector
         | VecTriple Vector Vector Vector

data Vector = DataVector DataVector
            | MapVector MapVector
            deriving (Show)

data DataVector =
    -- | A materialized data vector
      MVec !DataNode
    -- | A general delayed data vector
    | DVec !DelayedVector
    deriving (Show)

-- | A delayed data vector with a chain of replication vectors
data DelayedVector = DelayedVector
    { dvPropVec ::  !MapNode
    , dvPhysVec ::  !DataNode
    , dvSegments :: !Segments
    } deriving (Show)

data Segments = Segs | UnitSeg deriving (Show)

data MapVector = RVec !MapNode
               | SVec !MapNode
               | FVec !MapNode
               | KVec !MapNode
               deriving (Show)

class Node a where
    inject :: AlgNode -> a
    extract :: a -> AlgNode

newtype MapNode = MapNode { mapNode :: AlgNode } deriving (Show)
newtype DataNode = DataNode { dataNode :: AlgNode } deriving (Show)

instance Node MapNode where
    inject = MapNode
    extract (MapNode n) = n

instance Node DataNode where
    inject = DataNode
    extract (DataNode n) = n

dVec :: MapNode -> DataNode -> Vector
dVec m d = DataVector $ DVec $ DelayedVector m d Segs

uVec :: MapNode -> DataNode -> Vector
uVec m d = DataVector $ DVec $ DelayedVector m d UnitSeg

mVec :: DataNode -> Vector
mVec = DataVector . MVec

kVec :: MapNode -> Vector
kVec = MapVector . KVec

rVec :: MapNode -> Vector
rVec = MapVector . RVec

sVec :: MapNode -> Vector
sVec = MapVector . SVec

--------------------------------------------------------------------------------

lookupNode :: AlgNode -> VecBuild SL
lookupNode n = do
    m <- ask
    case IM.lookup n m of
        Just op -> return op
        Nothing -> error $ printf "SL2VSL: node %d not in SL nodes map %s " n (show m)

insertVirtOp :: VSL -> VecBuild AlgNode
insertVirtOp op = (lift . lift) (B.insert op)

bindOp :: Node a => VSL -> VecBuild a
bindOp op = inject <$> insertVirtOp op

bindOp2 :: (Node a, Node b) => VSL -> VecBuild (a, b)
bindOp2 op = do
    opNode <- insertVirtOp op
    r1Node <- inject <$> (insertVirtOp $ UnOp VSL.R1 opNode)
    r2Node <- inject <$> (insertVirtOp $ UnOp VSL.R2 opNode)
    return (r1Node, r2Node)

bindOp3 :: (Node a, Node b, Node c) => VSL -> VecBuild (a, b, c)
bindOp3 op = do
    opNode <- insertVirtOp op
    r1Node <- inject <$> (insertVirtOp $ UnOp VSL.R1 opNode)
    r2Node <- inject <$> (insertVirtOp $ UnOp VSL.R2 opNode)
    r3Node <- inject <$> (insertVirtOp $ UnOp VSL.R3 opNode)
    return (r1Node, r2Node, r3Node)

{-

class Node a where
    toNode   :: a -> AlgNode
    fromNode :: AlgNode -> a

BinOp :: (Node a, Node b) => (a -> b -> c) -> a -> b -> c

-}

materialize :: DataVector -> VecBuild DataNode
materialize (MVec n) = return n
materialize (DVec (DelayedVector segMap physVec _)) = do
    bindOp $ BinOp VSL.Materialize (mapNode segMap) (dataNode physVec)

withCache :: AlgNode -> (AlgNode -> VecBuild Res) -> VecBuild Res
withCache node f = do
    mRes <- gets (IM.lookup node)
    case mRes of
        Just res -> return res
        Nothing  -> f node

--------------------------------------------------------------------------------


-- onPhysical :: DataVector -> (AlgNode -> VecBuild Res) -> (Vector -> Res) -> VecBuild Res
-- onPhysical (MVec n) opConst = opConst n

--------------------------------------------------------------------------------

virtualize :: AlgNode -> VecBuild Res
virtualize node = withCache node translate

translate :: AlgNode -> VecBuild Res
translate node = do
    slOp <- lookupNode node
    case slOp of
        TerOp t c1 c2 c3 -> do
            r1 <- translate c1
            r2 <- translate c2
            r3 <- translate c3
            translateTerOp t r1 r2 r3
        BinOp b c1 c2    -> do
            r1 <- translate c1
            r2 <- translate c2
            translateBinOp b r1 r2
        UnOp u c1        -> do
            r1 <- translate c1
            translateUnOp u r1
        NullaryOp o      ->
            translateNullOp o

translateTerOp :: SL.TerOp -> Res -> Res -> Res -> VecBuild Res
translateTerOp SL.Combine (Vec (DataVector v1)) (Vec (DataVector v2)) (Vec (DataVector v3)) = do
    mv1 <- materialize v1
    mv2 <- materialize v2
    mv3 <- materialize v3
    (dv, kv1, kv2) <- bindOp3 $ TerOp VSL.Combine (dataNode mv1) (dataNode mv2) (dataNode mv3)
    return $ VecTriple (mVec dv) (kVec kv1) (kVec kv2)

translateBinOp :: SL.BinOp -> Res -> Res -> VecBuild Res
translateBinOp SL.ReplicateNest (Vec (DataVector v1)) (Vec (DataVector v2)) = do
    mv1 <- materialize v1
    mv2 <- materialize v2
    (d, r) <- bindOp2 $ BinOp VSL.ReplicateNest (dataNode mv1) (dataNode mv2)
    return $ VecPair (mVec d) (rVec r)
translateBinOp SL.ReplicateScalar (Vec (DataVector v1)) (Vec (DataVector v2)) = do
    -- Invariant: We know statically that the left input of a replicate operator
    -- will always be a unit vector.
    mv1 <- materialize v1
    -- TODO deal with a delayed vector v2
    mv2 <- materialize v2
    (d, r) <- bindOp2 $ BinOp VSL.ReplicateScalar (dataNode mv1) (dataNode mv2)
    return $ VecPair (mVec d) (rVec r)
translateBinOp SL.ReplicateVector (Vec (DataVector v1)) (Vec (DataVector v2)) = do
    -- Invariant: the left input of a replicate operator will always be a unit
    -- vector and consequently materialized.
    mv1 <- materialize v1
    -- TODO deal with a delayed vector v2
    mv2 <- materialize v2
    -- Generate a segment map that maps every segment induced by the right input
    -- to the unit segment.
    outerMap <- bindOp $ UnOp VSL.RepUnit (dataNode mv2)
    -- Generate a segment map that maps every key of the replication result to
    -- the corresponding segment in an inner vector connected to v1
    innerMap <- bindOp $ BinOp VSL.RepMap (mapNode outerMap) (dataNode mv1)

    return $ VecPair (dVec outerMap mv1)
                     (rVec innerMap)

translateBinOp SL.AppKey (Vec (MapVector m)) (Vec (DataVector d)) =
    undefined

translateBinOp SL.AppSort (Vec (MapVector m)) (Vec (DataVector d)) =
    undefined

translateBinOp SL.AppFilter (Vec (MapVector m)) (Vec (DataVector d)) =
    undefined

translateBinOp SL.AppRep (Vec (MapVector m)) (Vec (DataVector d)) =
    undefined

translateBinOp SL.UnboxSng (Vec (DataVector d1)) (Vec (DataVector d2)) = do
    md1 <- materialize d1
    md2 <- materialize d2
    (d, k) <- bindOp2 $ BinOp VSL.UnboxSng (dataNode md1) (dataNode md2)
    return $ VecPair (mVec d) (kVec k)

translateBinOp SL.UnboxSng (Vec (DataVector d1)) (Vec (DataVector d2)) = do
    md1 <- materialize d1
    md2 <- materialize d2
    d <- bindOp $ BinOp VSL.Align (dataNode md1) (dataNode md2)
    return $ Vec $ mVec d

-- FIXME aggrseg should not materialize but work only on physical segments. For
-- this, the handling of default values needs to move out of the operator.
translateBinOp (SL.AggrSeg as) (Vec (DataVector d1)) (Vec (DataVector d2)) = do
    md1 <- materialize d1
    md2 <- materialize d2
    d   <- bindOp $ BinOp (VSL.AggrSeg as) (dataNode md1) (dataNode md2)
    return $ Vec $ mVec d

translateBinOp SL.Append (Vec (DataVector d1)) (Vec (DataVector d2)) = do
    md1 <- materialize d1
    md2 <- materialize d2
    (d, k1, k2)   <- bindOp3 $ BinOp VSL.Append (dataNode md1) (dataNode md2)
    return $ VecTriple (mVec d) (kVec k1) (kVec k2)

translateBinOp SL.Zip (Vec (DataVector d1)) (Vec (DataVector d2)) = do
    md1 <- materialize d1
    md2 <- materialize d2
    (d, k1, k2)   <- bindOp3 $ BinOp VSL.Zip (dataNode md1) (dataNode md2)
    return $ VecTriple (mVec d) (kVec k1) (kVec k2)

translateBinOp (SL.ThetaJoin ps) (Vec (DataVector d1)) (Vec (DataVector d2)) = do
    case (d1, d2) of
        (MVec n1, MVec n2) -> do
            (d, r1, r2) <- bindOp3 $ BinOp (VSL.ThetaJoinMM ps) (dataNode n1) (dataNode n2)
            return $ VecTriple (mVec d) (rVec r1) (rVec r2)
        (DVec dv1, DVec dv2) -> do
            (d, r1, r2) <- bindOp3 $ BinOp (VSL.ThetaJoinMM ps) (dataNode $ dvPhysVec dv1)
                                                                (dataNode $ dvPhysVec dv2)

            -- We need to produce a segment map for any inner vectors of the left input that
            --
            -- (a) aligns the inner vector with the join result
            sm1         <- bindOp $ BinOp VSL.RepMap (dvSegMap dv1) (dataNode d)
            sm1'        <- bindOp $ BinOp VSL.UpdateSegMap (mapNode sm1) (mapNode r1)
            
            return $ VecTriple (dVec (dvSegMap dv1) d)
                               (rVec r1)
                               (rVec r2)

translateUnOp :: SL.UnOp -> Res -> VecBuild Res
translateUnOp SL.R1 (VecPair v1 _)     = return $ Vec v1
translateUnOp SL.R1 (VecTriple v1 _ _) = return $ Vec v1
translateUnOp SL.R2 (VecPair _ v2)     = return $ Vec v2
translateUnOp SL.R2 (VecTriple _ v2 _) = return $ Vec v2
translateUnOp SL.R3 (VecTriple _ _ v3) = return $ Vec v3
-- FIXME if we can tile operators, materialization is not necessary.
-- https://trello.com/c/GRTTgM9m
translateUnOp SL.UnboxKey (Vec (DataVector v)) = do
    mv <- materialize v
    p  <- bindOp $ UnOp VSL.UnboxKey $ dataNode mv
    return $ Vec $ kVec p
-- FIXME is materialization really necessary here?
translateUnOp SL.Segment (Vec (DataVector v)) = do
    mv <- materialize v
    v  <- bindOp $ UnOp VSL.Segment $ dataNode mv
    return $ Vec $ mVec v
translateUnOp (SL.Sort es) (Vec (DataVector v)) =
    case v of
        MVec n -> do
            (d, p) <- bindOp2 $ UnOp (VSL.Sort es) (dataNode n)
            return $ VecPair (mVec d) (sVec p)
        DVec dv -> do
            (d, p) <- bindOp2 $ UnOp (VSL.Sort es) (dataNode $ dvPhysVec dv)
            return $ VecPair (DataVector $ DVec $ dv { dvPhysVec = d } )
                             (MapVector $ SVec p)
translateUnOp (SL.Select predExpr) (Vec (DataVector v)) =
    case v of
        MVec n -> do
            (d, p) <- bindOp2 $ UnOp (VSL.Select predExpr) (dataNode n)
            return $ VecPair (DataVector $ MVec d) (MapVector $ FVec p)
        DVec dv -> do
            (d, p) <- bindOp2 $ UnOp (VSL.Select predExpr) (dataNode $ dvPhysVec dv)
            return $ VecPair (DataVector $ DVec $ dv { dvPhysVec = d } )
                             (MapVector $ FVec p)
translateUnOp SL.Reverse (Vec (DataVector v)) =
    case v of
        MVec n -> do
            (d, p) <- bindOp2 $ UnOp VSL.Reverse (dataNode n)
            return $ VecPair (DataVector $ MVec d) (MapVector $ SVec p)
        DVec dv -> do
            (d, p) <- bindOp2 $ UnOp VSL.Reverse (dataNode $ dvPhysVec dv)
            return $ VecPair (DataVector $ DVec $ dv { dvPhysVec = d } )
                             (MapVector $ SVec p)
translateUnOp SL.Number (Vec (DataVector v)) =
    case v of
        MVec n -> do
            d <- bindOp $ UnOp VSL.Number (dataNode n)
            return $ Vec $ DataVector $ MVec d
        DVec dv -> do
            d <- bindOp $ UnOp VSL.Number (dataNode $ dvPhysVec dv)
            return $ Vec $ DataVector $ DVec $ dv { dvPhysVec = d}
translateUnOp (SL.WinFun winFuns) (Vec (DataVector v)) =
    case v of
        MVec n -> do
            d <- bindOp $ UnOp (VSL.WinFun winFuns) (dataNode n)
            return $ Vec $ DataVector $ MVec d
        DVec dv -> do
            d <- bindOp $ UnOp (VSL.WinFun winFuns) (dataNode $ dvPhysVec dv)
            return $ Vec $ DataVector $ DVec $ dv { dvPhysVec = d}
translateUnOp SL.Unique (Vec (DataVector v)) =
    case v of
        MVec n -> do
            d <- bindOp $ UnOp VSL.Unique (dataNode n)
            return $ Vec $ DataVector $ MVec d
        DVec dv -> do
            d <- bindOp $ UnOp VSL.Unique (dataNode $ dvPhysVec dv)
            return $ Vec $ DataVector $ DVec $ dv { dvPhysVec = d}
translateUnOp (SL.Project es) (Vec (DataVector v)) =
    case v of
        MVec n -> do
            d <- bindOp $ UnOp (VSL.Project es) (dataNode n)
            return $ Vec $ DataVector $ MVec d
        DVec dv -> do
            d <- bindOp $ UnOp (VSL.Project es) (dataNode $ dvPhysVec dv)
            return $ Vec $ DataVector $ DVec $ dv { dvPhysVec = d}
translateUnOp (SL.GroupAggr args) (Vec (DataVector v)) =
    case v of
        MVec n -> do
            d <- bindOp $ UnOp (VSL.GroupAggr args) (dataNode n)
            return $ Vec $ DataVector $ MVec d
        DVec dv -> do
            d <- bindOp $ UnOp (VSL.GroupAggr args) (dataNode $ dvPhysVec dv)
            return $ Vec $ DataVector $ DVec $ dv { dvPhysVec = d}
translateUnOp (SL.Aggr args) (Vec (DataVector v)) =
    case v of
        MVec n -> do
            d <- bindOp $ UnOp (VSL.Aggr args) (dataNode n)
            return $ Vec $ DataVector $ MVec d
        DVec dv -> error "SL2VSL: aggr can't be applied to delayed vector"

translateNullOp :: SL.NullOp -> VecBuild Res
translateNullOp (SL.Lit args)      = Vec . mVec <$> bindOp (NullaryOp $ VSL.Lit args)
translateNullOp (SL.TableRef args) = Vec . mVec <$> bindOp (NullaryOp $ VSL.TableRef args)
