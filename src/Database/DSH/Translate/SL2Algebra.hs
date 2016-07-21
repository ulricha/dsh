{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell  #-}

module Database.DSH.Translate.SL2Algebra
    ( VecBuild
    , runVecBuild
    , vl2Algebra
    ) where

import qualified Data.IntMap                    as IM
import           Data.List
import qualified Data.Traversable               as T

import           Control.Monad.State

import qualified Database.Algebra.Dag.Build     as B
import           Database.Algebra.Dag.Common

import           Database.DSH.Common.Impossible
import           Database.DSH.Common.QueryPlan
import qualified Database.DSH.Common.Vector as V
import qualified Database.DSH.SL.Lang           as SL
import           Database.DSH.SL.SegmentAlgebra

-- FIXME the vector types d r k f s are determined by the algebra a.
-- The only type variable necessary should be a.
type Cache d r k f s = IM.IntMap (Res d r k f s)

-- | A layer on top of the DAG builder monad that caches the
-- translation result of SL nodes.
type VecBuild a d r k f s = StateT (Cache d r k f s) (B.Build a)

runVecBuild :: SegmentAlgebra a
            => VecBuild a (SLDVec a) (SLRVec a) (SLKVec a) (SLFVec a) (SLSVec a) r
            -> B.Build a r
runVecBuild c = evalStateT c IM.empty

data Res d r k f s
    = RRVec r
    | RKVec k
    | RFVec f
    | RSVec s
    | RDVec d
    | RLPair (Res d r k f s) (Res d r k f s)
    | RTriple (Res d r k f s) (Res d r k f s) (Res d r k f s)
    deriving Show

fromDict :: SegmentAlgebra a => AlgNode -> VecBuild a d r k f s (Maybe (Res d r k f s))
fromDict n = gets (IM.lookup n)

insertTranslation :: SegmentAlgebra a => AlgNode -> Res d r k f s -> VecBuild a d r k f s ()
insertTranslation n res = modify (IM.insert n res)

--------------------------------------------------------------------------------
-- Wrappers and unwrappers for vector references

fromRVec :: r -> Res d r k f s
fromRVec p = RRVec p

fromKVec :: k -> Res d r k f s
fromKVec r = RKVec r

fromDVec :: d -> Res d r k f s
fromDVec v = RDVec v

fromFVec :: f -> Res d r k f s
fromFVec v = RFVec v

fromSVec :: s -> Res d r k f s
fromSVec v = RSVec v

toDVec :: Res d r k f s -> d
toDVec (RDVec v) = v
toDVec _         = error "toDVec: Not a RDVec"

toRVec :: Res d r k f s -> r
toRVec (RRVec p) = p
toRVec _         = error "toRVec: Not a replication vector"

toKVec :: Res d r k f s -> k
toKVec (RKVec r) = r
toKVec _         = error "toKVec: Not a rekeying vector"

toFVec :: Res d r k f s -> f
toFVec (RFVec r) = r
toFVec _         = error "toFVec: Not a filtering vector"

toSVec :: Res d r k f s -> s
toSVec (RSVec r) = r
toSVec _         = error "toSVec: Not a filtering vector"

--------------------------------------------------------------------------------

-- | Refresh vectors in a shape from the cache.
refreshShape :: SegmentAlgebra a => Shape V.DVec -> VecBuild a d r k f s (Shape d)
refreshShape shape = T.mapM refreshVec shape
  where
    refreshVec (V.DVec n) = do
        mv <- fromDict n
        case mv of
            Just v -> return $ toDVec v
            Nothing -> $impossible

translate :: SegmentAlgebra a
          => NodeMap SL.SL
          -> AlgNode
          -> VecBuild a (SLDVec a) (SLRVec a) (SLKVec a) (SLFVec a) (SLSVec a) (Res (SLDVec a) (SLRVec a) (SLKVec a) (SLFVec a) (SLSVec a))
translate vlNodes n = do
    r <- fromDict n

    case r of
        -- The SL node has already been encountered and translated.
        Just res -> return $ res

        -- The SL node has not been translated yet.
        Nothing  -> do
            let vlOp = getSL n vlNodes
            r' <- case vlOp of
                TerOp t c1 c2 c3 -> do
                    c1' <- translate vlNodes c1
                    c2' <- translate vlNodes c2
                    c3' <- translate vlNodes c3
                    lift $ translateTerOp t c1' c2' c3'
                BinOp b c1 c2    -> do
                    c1' <- translate vlNodes c1
                    c2' <- translate vlNodes c2
                    lift $ translateBinOp b c1' c2'
                UnOp u c1        -> do
                    c1' <- translate vlNodes c1
                    lift $ translateUnOp u c1'
                NullaryOp o      -> lift $ translateNullary o

            insertTranslation n r'
            return r'

getSL :: AlgNode -> NodeMap SL.SL -> SL.SL
getSL n vlNodes = case IM.lookup n vlNodes of
    Just op -> op
    Nothing -> error $ "getSL: node " ++ (show n) ++ " not in SL nodes map " ++ (pp vlNodes)

pp :: NodeMap SL.SL -> String
pp m = intercalate ",\n" $ map show $ IM.toList m

vl2Algebra :: SegmentAlgebra a => NodeMap SL.SL -> Shape V.DVec -> B.Build a (Shape (SLDVec a))
vl2Algebra vlNodes plan = runVecBuild $ do
    mapM_ (translate vlNodes) roots
    refreshShape plan
  where
    roots :: [AlgNode]
    roots = shapeNodes plan

translateTerOp :: SegmentAlgebra a
               => SL.TerOp
               -> Res (SLDVec a) (SLRVec a) (SLKVec a) (SLFVec a) (SLSVec a)
               -> Res (SLDVec a) (SLRVec a) (SLKVec a) (SLFVec a) (SLSVec a)
               -> Res (SLDVec a) (SLRVec a) (SLKVec a) (SLFVec a) (SLSVec a)
               -> B.Build a (Res (SLDVec a) (SLRVec a) (SLKVec a) (SLFVec a) (SLSVec a))
translateTerOp t c1 c2 c3 =
    case t of
        SL.Combine -> do
            (d, r1, r2) <- vecCombine (toDVec c1) (toDVec c2) (toDVec c3)
            return $ RTriple (fromDVec d) (fromKVec r1) (fromKVec r2)

translateBinOp :: SegmentAlgebra a
               => SL.BinOp
               -> Res (SLDVec a) (SLRVec a) (SLKVec a) (SLFVec a) (SLSVec a)
               -> Res (SLDVec a) (SLRVec a) (SLKVec a) (SLFVec a) (SLSVec a)
               -> B.Build a (Res (SLDVec a) (SLRVec a) (SLKVec a) (SLFVec a) (SLSVec a))
translateBinOp b c1 c2 = case b of
    SL.ReplicateNest -> do
        (v, p) <- vecReplicateNest (toDVec c1) (toDVec c2)
        return $ RLPair (fromDVec v) (fromRVec p)

    SL.ReplicateScalar -> do
        (v, p) <- vecReplicateScalar (toDVec c1) (toDVec c2)
        return $ RLPair (fromDVec v) (fromRVec p)

    SL.ReplicateVector -> do
        (v, p) <- vecReplicateVector (toDVec c1) (toDVec c2)
        return $ RLPair (fromDVec v) (fromRVec p)

    SL.AppKey -> do
        (v, k) <- vecAppKey (toKVec c1) (toDVec c2)
        return $ RLPair (fromDVec v) (fromKVec k)

    SL.AppSort -> do
        (v, s) <- vecAppSort (toSVec c1) (toDVec c2)
        return $ RLPair (fromDVec v) (fromSVec s)

    SL.AppRep -> do
        (v, r) <- vecAppRep (toRVec c1) (toDVec c2)
        return $ RLPair (fromDVec v) (fromRVec r)

    SL.AppFilter -> do
        (v, f) <- vecAppFilter (toFVec c1) (toDVec c2)
        return $ RLPair (fromDVec v) (fromFVec f)

    SL.UnboxSng -> do
        (v, k) <- vecUnboxSng (toDVec c1) (toDVec c2)
        return $ RLPair (fromDVec v) (fromKVec k)

    SL.Append -> do
        (v, r1, r2) <- vecAppend (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec v) (fromKVec r1) (fromKVec r2)

    SL.AggrSeg a -> fromDVec <$> vecAggrSeg a (toDVec c1) (toDVec c2)

    SL.Align -> fromDVec <$> vecAlign (toDVec c1) (toDVec c2)

    SL.Zip -> do
        (v, r1 ,r2) <- vecZip (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec v) (fromKVec r1) (fromKVec r2)

    SL.CartProduct -> do
        (v, p1, p2) <- vecCartProduct (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec v) (fromRVec p1) (fromRVec p2)

    SL.ThetaJoin p -> do
        (v, p1, p2) <- vecThetaJoin p (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec v) (fromRVec p1) (fromRVec p2)

    SL.NestJoin p -> do
        (v, p1, p2) <- vecNestJoin p (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec v) (fromRVec p1) (fromRVec p2)

    SL.GroupJoin (p, as) -> fromDVec <$> vecGroupJoin p as (toDVec c1) (toDVec c2)

    SL.SemiJoin p -> do
        (v, r) <- vecSemiJoin p (toDVec c1) (toDVec c2)
        return $ RLPair (fromDVec v) (fromFVec r)

    SL.AntiJoin p -> do
        (v, r) <- vecAntiJoin p (toDVec c1) (toDVec c2)
        return $ RLPair (fromDVec v) (fromFVec r)

translateUnOp :: SegmentAlgebra a
              => SL.UnOp
              -> Res (SLDVec a) (SLRVec a) (SLKVec a) (SLFVec a) (SLSVec a)
              -> B.Build a (Res (SLDVec a) (SLRVec a) (SLKVec a) (SLFVec a) (SLSVec a))
translateUnOp unop c = case unop of
    SL.Unique          -> fromDVec <$> vecUnique (toDVec c)
    SL.Number          -> fromDVec <$> vecNumber (toDVec c)
    SL.UnboxKey         -> fromKVec <$> vecUnboxKey (toDVec c)
    SL.WinFun  (a, w)   -> fromDVec <$> vecWinFun a w (toDVec c)
    SL.Segment          -> fromDVec <$> vecSegment (toDVec c)
    SL.Unsegment        -> fromDVec <$> vecUnsegment (toDVec c)
    SL.Select e         -> do
        (d, r) <- vecSelect e (toDVec c)
        return $ RLPair (fromDVec d) (fromFVec r)
    SL.Sort es         -> do
        (d, p) <- vecSort es (toDVec c)
        return $ RLPair (fromDVec d) (fromSVec p)
    SL.Group es -> do
        (qo, qi, p) <- vecGroup es (toDVec c)
        return $ RTriple (fromDVec qo) (fromDVec qi) (fromSVec p)
    SL.Project cols -> fromDVec <$> vecProject cols (toDVec c)
    SL.Reverse      -> do
        (d, p) <- vecReverse (toDVec c)
        return $ RLPair (fromDVec d) (fromSVec p)
    SL.GroupAggr (g, as) -> fromDVec <$> vecGroupAggr g as (toDVec c)

    SL.R1            -> case c of
        (RLPair c1 _)     -> return c1
        (RTriple c1 _ _) -> return c1
        _                -> error "R1: Not a tuple"
    SL.R2            -> case c of
        (RLPair _ c2)     -> return c2
        (RTriple _ c2 _) -> return c2
        _                -> error "R2: Not a tuple"
    SL.R3            -> case c of
        (RTriple _ _ c3) -> return c3
        _                -> error "R3: Not a tuple"

translateNullary :: SegmentAlgebra a
                 => SL.NullOp
                 -> B.Build a (Res (SLDVec a) (SLRVec a) (SLKVec a) (SLFVec a) (SLSVec a))
translateNullary (SL.Lit (tys, frame, segs)) = fromDVec <$> vecLit tys frame segs
translateNullary (SL.TableRef (n, schema))   = fromDVec <$> vecTableRef n schema
