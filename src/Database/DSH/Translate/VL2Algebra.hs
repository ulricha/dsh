{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE FlexibleContexts #-}

module Database.DSH.Translate.VL2Algebra
    ( VecBuild
    , runVecBuild
    , vl2Algebra
    ) where

import qualified Data.IntMap                          as IM
import           Data.List
import qualified Data.Map                             as M
import qualified Data.Traversable                     as T

import           Control.Monad.State

import qualified Database.Algebra.Dag                 as D
import qualified Database.Algebra.Dag.Build           as B
import           Database.Algebra.Dag.Common

import           Database.DSH.Common.Impossible
import           Database.DSH.Common.QueryPlan
import           Database.DSH.Translate.FKL2VL        ()
import           Database.DSH.Common.Vector
import qualified Database.DSH.VL.Lang                 as V
import           Database.DSH.VL.VectorAlgebra

-- FIXME the vector types d r k f s are determined by the algebra a.
-- The only type variable necessary should be a.
type Cache d r k f s = M.Map AlgNode (Res d r k f s)

-- | A layer on top of the DAG builder monad that caches the
-- translation result of VL nodes.
type VecBuild a d r k f s = StateT (Cache d r k f s) (B.Build a)

runVecBuild :: VectorAlgebra a
            => VecBuild a (DVec a) (RVec a) (KVec a) (FVec a) (SVec a) r
            -> (D.AlgebraDag a, r, NodeMap [Tag])
runVecBuild c = B.runBuild $ fst <$> runStateT c M.empty

data Res d r k f s
    = RRVec r
    | RKVec k
    | RFVec f
    | RSVec s
    | RDVec d
    | RLPair (Res d r k f s) (Res d r k f s)
    | RTriple (Res d r k f s) (Res d r k f s) (Res d r k f s)
    deriving Show

fromDict :: VectorAlgebra a => AlgNode -> VecBuild a d r k f s (Maybe (Res d r k f s))
fromDict n = do
    dict <- get
    return $ M.lookup n dict

insertTranslation :: VectorAlgebra a => AlgNode -> Res d r k f s -> VecBuild a d r k f s ()
insertTranslation n res = modify (M.insert n res)

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
toDVec _         = error "toDVec: Not a NDVec"

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
refreshShape :: VectorAlgebra a => Shape VLDVec -> VecBuild a d r k f s (Shape d)
refreshShape shape = T.mapM refreshVec shape
  where
    refreshVec (VLDVec n) = do
        mv <- fromDict n
        case mv of
            Just v -> return $ toDVec v
            Nothing -> $impossible

translate :: VectorAlgebra a
          => NodeMap V.VL
          -> AlgNode
          -> VecBuild a (DVec a) (RVec a) (KVec a) (FVec a) (SVec a) (Res (DVec a) (RVec a) (KVec a) (FVec a) (SVec a))
translate vlNodes n = do
    r <- fromDict n

    case r of
        -- The VL node has already been encountered and translated.
        Just res -> return $ res

        -- The VL node has not been translated yet.
        Nothing  -> do
            let vlOp = getVL n vlNodes
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

getVL :: AlgNode -> NodeMap V.VL -> V.VL
getVL n vlNodes = case IM.lookup n vlNodes of
    Just op -> op
    Nothing -> error $ "getVL: node " ++ (show n) ++ " not in VL nodes map " ++ (pp vlNodes)

pp :: NodeMap V.VL -> String
pp m = intercalate ",\n" $ map show $ IM.toList m

vl2Algebra :: VectorAlgebra a
           => NodeMap V.VL
           -> Shape VLDVec
           -> VecBuild a (DVec a) (RVec a) (KVec a) (FVec a) (SVec a) (Shape (DVec a))
vl2Algebra vlNodes plan = do
    mapM_ (translate vlNodes) roots

    refreshShape plan
  where
    roots :: [AlgNode]
    roots = shapeNodes plan

translateTerOp :: VectorAlgebra a
               => V.TerOp
               -> Res (DVec a) (RVec a) (KVec a) (FVec a) (SVec a)
               -> Res (DVec a) (RVec a) (KVec a) (FVec a) (SVec a)
               -> Res (DVec a) (RVec a) (KVec a) (FVec a) (SVec a)
               -> B.Build a (Res (DVec a) (RVec a) (KVec a) (FVec a) (SVec a))
translateTerOp t c1 c2 c3 =
    case t of
        V.Combine -> do
            (d, r1, r2) <- vecCombine (toDVec c1) (toDVec c2) (toDVec c3)
            return $ RTriple (fromDVec d) (fromKVec r1) (fromKVec r2)

translateBinOp :: VectorAlgebra a
               => V.BinOp
               -> Res (DVec a) (RVec a) (KVec a) (FVec a) (SVec a)
               -> Res (DVec a) (RVec a) (KVec a) (FVec a) (SVec a)
               -> B.Build a (Res (DVec a) (RVec a) (KVec a) (FVec a) (SVec a))
translateBinOp b c1 c2 = case b of
    V.DistLift -> do
        (v, p) <- vecDistLift (toDVec c1) (toDVec c2)
        return $ RLPair (fromDVec v) (fromRVec p)

    V.AppKey -> do
        (v, k) <- vecAppKey (toKVec c1) (toDVec c2)
        return $ RLPair (fromDVec v) (fromKVec k)

    V.AppSort -> do
        (v, s) <- vecAppSort (toSVec c1) (toDVec c2)
        return $ RLPair (fromDVec v) (fromSVec s)

    V.AppRep -> do
        (v, r) <- vecAppRep (toRVec c1) (toDVec c2)
        return $ RLPair (fromDVec v) (fromRVec r)

    V.AppFilter -> do
        (v, f) <- vecAppFilter (toFVec c1) (toDVec c2)
        return $ RLPair (fromDVec v) (fromFVec f)

    V.UnboxScalar -> RDVec <$> vecUnboxScalar (toDVec c1) (toDVec c2)

    V.Append -> do
        (v, r1, r2) <- vecAppend (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec v) (fromKVec r1) (fromKVec r2)

    V.AppendS -> do
        (v, r1, r2) <- vecAppendS (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec v) (fromKVec r1) (fromKVec r2)

    V.AggrS a -> fromDVec <$> vecAggrS a (toDVec c1) (toDVec c2)


    V.Zip -> do
        (v, f1, f2) <- vecZip (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec v) (fromKVec f1) (fromKVec f2)

    V.Align -> fromDVec <$> vecAlign (toDVec c1) (toDVec c2)

    V.ZipS -> do
        (v, r1 ,r2) <- vecZipS (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec v) (fromKVec r1) (fromKVec r2)

    V.CartProduct -> do
        (v, p1, p2) <- vecCartProduct (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec v) (fromRVec p1) (fromRVec p2)

    V.CartProductS -> do
        (v, p1, p2) <- vecCartProductS (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec v) (fromRVec p1) (fromRVec p2)

    V.NestProductS -> do
        (v, p1, p2) <- vecNestProductS (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec v) (fromRVec p1) (fromRVec p2)

    V.ThetaJoin p -> do
        (v, p1, p2) <- vecThetaJoin p (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec v) (fromRVec p1) (fromRVec p2)

    V.NestProduct -> do
        (v, p1, p2) <- vecNestProduct (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec v) (fromRVec p1) (fromRVec p2)

    V.NestJoin p -> do
        (v, p1, p2) <- vecNestJoin p (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec v) (fromRVec p1) (fromRVec p2)

    V.ThetaJoinS p -> do
        (v, p1, p2) <- vecThetaJoinS p (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec v) (fromRVec p1) (fromRVec p2)

    V.NestJoinS p -> do
        (v, p1, p2) <- vecNestJoinS p (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec v) (fromRVec p1) (fromRVec p2)

    V.GroupJoin (p, a) -> fromDVec <$> vecGroupJoin p a (toDVec c1) (toDVec c2)

    V.SemiJoin p -> do
        (v, r) <- vecSemiJoin p (toDVec c1) (toDVec c2)
        return $ RLPair (fromDVec v) (fromFVec r)

    V.SemiJoinS p -> do
        (v, r) <- vecSemiJoinS p (toDVec c1) (toDVec c2)
        return $ RLPair (fromDVec v) (fromFVec r)

    V.AntiJoin p -> do
        (v, r) <- vecAntiJoin p (toDVec c1) (toDVec c2)
        return $ RLPair (fromDVec v) (fromFVec r)

    V.AntiJoinS p -> do
        (v, r) <- vecAntiJoinS p (toDVec c1) (toDVec c2)
        return $ RLPair (fromDVec v) (fromFVec r)

    V.TransposeS -> do
        (qo, qi) <- vecTransposeS (toDVec c1) (toDVec c2)
        return $ RLPair (fromDVec qo) (fromDVec qi)

translateUnOp :: VectorAlgebra a
              => V.UnOp
              -> Res (DVec a) (RVec a) (KVec a) (FVec a) (SVec a)
              -> B.Build a (Res (DVec a) (RVec a) (KVec a) (FVec a) (SVec a))
translateUnOp unop c = case unop of
    V.Unique           -> fromDVec <$> vecUnique (toDVec c)
    V.UniqueS          -> fromDVec <$> vecUniqueS (toDVec c)
    V.Number           -> fromDVec <$> vecNumber (toDVec c)
    V.NumberS          -> fromDVec <$> vecNumberS (toDVec c)
    V.UnboxKey         -> fromKVec <$> vecUnboxKey (toDVec c)
    V.Segment          -> fromDVec <$> vecSegment (toDVec c)
    V.Unsegment        -> fromDVec <$> vecUnsegment (toDVec c)
    V.Aggr a           -> fromDVec <$> vecAggr a (toDVec c)
    V.WinFun  (a, w)   -> fromDVec <$> vecWinFun a w (toDVec c)
    V.Select e         -> do
        (d, r) <- vecSelect e (toDVec c)
        return $ RLPair (fromDVec d) (fromFVec r)
    V.Sort es         -> do
        (d, p) <- vecSort es (toDVec c)
        return $ RLPair (fromDVec d) (fromSVec p)
    V.SortS es         -> do
        (d, p) <- vecSortS es (toDVec c)
        return $ RLPair (fromDVec d) (fromSVec p)
    V.Group es -> do
        (qo, qi, p) <- vecGroup es (toDVec c)
        return $ RTriple (fromDVec qo) (fromDVec qi) (fromSVec p)
    V.GroupS es -> do
        (qo, qi, p) <- vecGroupS es (toDVec c)
        return $ RTriple (fromDVec qo) (fromDVec qi) (fromSVec p)
    V.Project cols -> fromDVec <$> vecProject cols (toDVec c)
    V.Reverse      -> do
        (d, p) <- vecReverse (toDVec c)
        return $ RLPair (fromDVec d) (fromSVec p)
    V.ReverseS      -> do
        (d, p) <- vecReverseS (toDVec c)
        return $ RLPair (fromDVec d) (fromSVec p)
    V.GroupAggr (g, as) -> fromDVec <$> vecGroupAggr g as (toDVec c)

    V.Reshape n -> do
        (qo, qi) <- vecReshape n (toDVec c)
        return $ RLPair (fromDVec qo) (fromDVec qi)
    V.ReshapeS n -> do
        (qo, qi) <- vecReshapeS n (toDVec c)
        return $ RLPair (fromDVec qo) (fromDVec qi)
    V.Transpose -> do
        (qo, qi) <- vecTranspose (toDVec c)
        return $ RLPair (fromDVec qo) (fromDVec qi)

    V.Nest -> do
        (qo, qi) <- vecNest (toDVec c)
        return $ RLPair (fromDVec qo) (fromDVec qi)

    V.R1            -> case c of
        (RLPair c1 _)     -> return c1
        (RTriple c1 _ _) -> return c1
        _                -> error "R1: Not a tuple"
    V.R2            -> case c of
        (RLPair _ c2)     -> return c2
        (RTriple _ c2 _) -> return c2
        _                -> error "R2: Not a tuple"
    V.R3            -> case c of
        (RTriple _ _ c3) -> return c3
        _                -> error "R3: Not a tuple"

translateNullary :: VectorAlgebra a
                 => V.NullOp
                 -> B.Build a (Res (DVec a) (RVec a) (KVec a) (FVec a) (SVec a))
translateNullary (V.Lit (_, tys, vals))    = fromDVec <$> vecLit tys vals
translateNullary (V.TableRef (n, schema))  = fromDVec <$> vecTableRef n schema
