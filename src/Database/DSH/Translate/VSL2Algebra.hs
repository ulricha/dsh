{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell  #-}

module Database.DSH.Translate.VSL2Algebra
    ( VecBuild
    , runVecBuild
    , vl2Algebra
    ) where

import qualified Data.IntMap                            as IM
import           Data.List
import qualified Data.Traversable                       as T

import           Control.Monad.State

import qualified Database.Algebra.Dag.Build             as B
import           Database.Algebra.Dag.Common

import           Database.DSH.Common.Impossible
import           Database.DSH.Common.QueryPlan
import qualified Database.DSH.Common.Vector             as V
import           Database.DSH.Common.VectorLang
import qualified Database.DSH.VSL.Lang                  as VSL
import           Database.DSH.VSL.VirtualSegmentAlgebra

-- FIXME the vector types d r are determined by the algebra a.
-- The only type variable necessary should be a.
type Cache d r = IM.IntMap (Res d r)

-- | A layer on top of the DAG builder monad that caches the
-- translation result of VSL nodes.
type VecBuild a d r = StateT (Cache d r) (B.Build a)

runVecBuild :: VecBuild a (VSLDVec a) (VSLRVec a) r -> B.Build a r
runVecBuild c = evalStateT c IM.empty

data Res d r
    = RRVec r
    | RDVec d
    | RLPair (Res d r) (Res d r)
    | RTriple (Res d r) (Res d r) (Res d r)
    deriving Show

fromDict :: AlgNode -> VecBuild a d r (Maybe (Res d r))
fromDict n = gets (IM.lookup n)

insertTranslation :: AlgNode -> Res d r -> VecBuild a d r ()
insertTranslation n res = modify (IM.insert n res)

--------------------------------------------------------------------------------
-- Wrappers and unwrappers for vector references

fromRVec :: r -> Res d r
fromRVec p = RRVec p

fromDVec :: d -> Res d r
fromDVec v = RDVec v

toDVec :: Res d r -> d
toDVec (RDVec v) = v
toDVec _         = error "toDVec: Not a RDVec"

toRVec :: Res d r -> r
toRVec (RRVec p) = p
toRVec _         = error "toRVec: Not a replication vector"

--------------------------------------------------------------------------------

-- | Refresh vectors in a shape from the cache.
refreshShape :: VirtualSegmentAlgebra a => Shape V.DVec -> VecBuild a d r (Shape d)
refreshShape shape = T.mapM refreshVec shape
  where
    refreshVec (V.DVec n) = do
        mv <- fromDict n
        case mv of
            Just v -> return $ toDVec v
            Nothing -> $impossible

translate :: VirtualSegmentAlgebra a
          => NodeMap VSL.RVSL
          -> AlgNode
          -> VecBuild a (VSLDVec a) (VSLRVec a) (Res (VSLDVec a) (VSLRVec a))
translate vlNodes n = do
    r <- fromDict n

    case r of
        -- The VSL node has already been encountered and translated.
        Just res -> return $ res

        -- The VSL node has not been translated yet.
        Nothing  -> do
            let vlOp = getVSL n vlNodes
            r' <- case VSL.unVSL vlOp of
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

getVSL :: AlgNode -> NodeMap VSL.RVSL -> VSL.RVSL
getVSL n vlNodes = case IM.lookup n vlNodes of
    Just op -> op
    Nothing -> error $ "getVSL: node " ++ (show n) ++ " not in VSL nodes map " ++ (pp vlNodes)

pp :: NodeMap VSL.RVSL -> String
pp m = intercalate ",\n" $ map show $ IM.toList m

vl2Algebra :: VirtualSegmentAlgebra a
           => NodeMap VSL.RVSL
           -> Shape V.DVec
           -> B.Build a (Shape (VSLDVec a))
vl2Algebra vlNodes plan = runVecBuild $ do
    mapM_ (translate vlNodes) roots
    refreshShape plan
  where
    roots :: [AlgNode]
    roots = shapeNodes plan

translateTerOp :: VirtualSegmentAlgebra a
               => VSL.TerOp
               -> Res (VSLDVec a) (VSLRVec a)
               -> Res (VSLDVec a) (VSLRVec a)
               -> Res (VSLDVec a) (VSLRVec a)
               -> B.Build a (Res (VSLDVec a) (VSLRVec a))
translateTerOp t c1 c2 c3 =
    case t of
        VSL.Combine -> do
            (d, r1, r2) <- vecCombine (toDVec c1) (toDVec c2) (toDVec c3)
            return $ RTriple (fromDVec d) (fromRVec r1) (fromRVec r2)

translateBinOp :: VirtualSegmentAlgebra a
               => VSL.BinOp RExpr
               -> Res (VSLDVec a) (VSLRVec a)
               -> Res (VSLDVec a) (VSLRVec a)
               -> B.Build a (Res (VSLDVec a) (VSLRVec a))
translateBinOp b c1 c2 = case b of
    VSL.ReplicateSeg -> do
        (v, p) <- vecReplicateSeg (toDVec c1) (toDVec c2)
        return $ RLPair (fromDVec v) (fromRVec p)

    VSL.ReplicateScalar -> do
        (v, p) <- vecReplicateScalar (toDVec c1) (toDVec c2)
        return $ RLPair (fromDVec v) (fromRVec p)

    VSL.Materialize -> do
        (v, p) <- vecMaterialize (toRVec c1) (toDVec c2)
        return $ RLPair (fromDVec v) (fromRVec p)

    VSL.UnboxSng -> do
        (v, k) <- vecUnboxSng (toDVec c1) (toDVec c2)
        return $ RLPair (fromDVec v) (fromRVec k)

    VSL.Append -> do
        (v, r1, r2) <- vecAppend (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec v) (fromRVec r1) (fromRVec r2)


    VSL.Align -> fromDVec <$> vecAlign (toDVec c1) (toDVec c2)

    VSL.Zip -> do
        (v, r1 ,r2) <- vecZip (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec v) (fromRVec r1) (fromRVec r2)

    VSL.CartProduct -> do
        (v, p1, p2) <- vecCartProduct (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec v) (fromRVec p1) (fromRVec p2)

    VSL.ThetaJoin (l1, l2, p) -> do
        (v, p1, p2) <- vecThetaJoin l1 l2 p (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec v) (fromRVec p1) (fromRVec p2)

    VSL.NestJoin (l1, l2, p) -> do
        (v, p1, p2) <- vecNestJoin l1 l2 p (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec v) (fromRVec p1) (fromRVec p2)

    VSL.GroupJoin (l1, l2, p, as) -> fromDVec <$> vecGroupJoin l1 l2 p as (toDVec c1) (toDVec c2)

    VSL.SemiJoin (l1, l2, p) -> do
        (v, r) <- vecSemiJoin l1 l2 p (toDVec c1) (toDVec c2)
        return $ RLPair (fromDVec v) (fromRVec r)

    VSL.AntiJoin (l1, l2, p) -> do
        (v, r) <- vecAntiJoin l1 l2 p (toDVec c1) (toDVec c2)
        return $ RLPair (fromDVec v) (fromRVec r)

    VSL.UnboxDefault vs -> do
        (v, r) <- vecUnboxDefault vs (toDVec c1) (toDVec c2)
        return $ RLPair (fromDVec v) (fromRVec r)

    VSL.UpdateMap -> fromRVec <$> vecUpdateMap (toRVec c1) (toRVec c2)

translateUnOp :: VirtualSegmentAlgebra a
              => VSL.UnOp VRow RExpr
              -> Res (VSLDVec a) (VSLRVec a)
              -> B.Build a (Res (VSLDVec a) (VSLRVec a))
translateUnOp unop c = case unop of
    VSL.Fold a           -> fromDVec <$> vecFold a (toDVec c)
    VSL.Distinct         -> fromDVec <$> vecDistinct (toDVec c)
    VSL.Number           -> fromDVec <$> vecNumber (toDVec c)
    VSL.MergeMap         -> fromRVec <$> vecMergeMap (toDVec c)
    VSL.WinFun  (a, w)   -> fromDVec <$> vecWinFun a w (toDVec c)
    VSL.Segment          -> fromDVec <$> vecSegment (toDVec c)
    VSL.Unsegment        -> fromDVec <$> vecUnsegment (toDVec c)
    VSL.Select e         -> do
        (d, r) <- vecSelect e (toDVec c)
        return $ RLPair (fromDVec d) (fromRVec r)
    VSL.Sort e         -> do
        (d, p) <- vecSort e (toDVec c)
        return $ RLPair (fromDVec d) (fromRVec p)
    VSL.Group es -> do
        (qo, qi, p) <- vecGroup es (toDVec c)
        return $ RTriple (fromDVec qo) (fromDVec qi) (fromRVec p)
    VSL.Project cols -> fromDVec <$> vecProject cols (toDVec c)
    VSL.Reverse      -> do
        (d, p) <- vecReverse (toDVec c)
        return $ RLPair (fromDVec d) (fromRVec p)
    VSL.GroupAggr (g, as) -> fromDVec <$> vecGroupAggr g as (toDVec c)

    VSL.UnitMap -> fromRVec <$> vecUnitMap (toDVec c)
    VSL.UpdateUnit -> fromRVec <$> vecUpdateUnit (toRVec c)

    VSL.R1            -> case c of
        (RLPair c1 _)     -> return c1
        (RTriple c1 _ _) -> return c1
        _                -> error "R1: Not a tuple"
    VSL.R2            -> case c of
        (RLPair _ c2)     -> return c2
        (RTriple _ c2 _) -> return c2
        _                -> error "R2: Not a tuple"
    VSL.R3            -> case c of
        (RTriple _ _ c3) -> return c3
        _                -> error "R3: Not a tuple"

translateNullary :: VirtualSegmentAlgebra a
                 => VSL.NullOp
                 -> B.Build a (Res (VSLDVec a) (VSLRVec a))
translateNullary (VSL.Lit (tys, segs))      = fromDVec <$> vecLit tys segs
translateNullary (VSL.TableRef (n, schema)) = fromDVec <$> vecTableRef n schema
