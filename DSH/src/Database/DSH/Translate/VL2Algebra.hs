{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Translate.VL2Algebra
    ( implementVectorOpsX100
    , implementVectorOpsPF
    ) where

import qualified Data.IntMap                          as IM
import           Data.List
import qualified Data.Map                             as M

import           Control.Applicative
import           Control.Monad.State

import           Database.Algebra.Dag
import           Database.Algebra.Dag.Builder
import           Database.Algebra.Dag.Common
import qualified Database.Algebra.Table.Lang          as TA
import           Database.Algebra.X100.Data           (X100Algebra)
import           Database.Algebra.X100.Data.Create    (dummy)

import           Database.DSH.Impossible
import           Database.DSH.Common.QueryPlan
import           Database.DSH.Translate.FKL2VL        ()
import           Database.DSH.VL.Data.DBVector
import qualified Database.DSH.VL.Lang                 as V
import           Database.DSH.VL.TAVectorPrimitives   ()
import           Database.DSH.VL.VectorPrimitives
import           Database.DSH.VL.X100VectorPrimitives ()

type G alg = StateT (M.Map AlgNode Res) (GraphM () alg)

runG :: VectorAlgebra a => a -> G a r -> AlgPlan a r
runG i c = runGraph i $ fst <$> runStateT c M.empty

data Res = Prop    AlgNode
         | Rename  AlgNode
         | RDVec   AlgNode [DBCol]
         | RPair   Res Res
         | RTriple Res Res Res
         deriving Show

fromDict :: VectorAlgebra a => AlgNode -> G a (Maybe Res)
fromDict n = do
    dict <- get
    return $ M.lookup n dict

insertTranslation :: VectorAlgebra a => AlgNode -> Res -> G a ()
insertTranslation n res = modify (M.insert n res)

fromPVec :: PVec -> Res
fromPVec (PVec p) = Prop p

toPVec :: Res -> PVec
toPVec (Prop p) = PVec p
toPVec _       = error "toPVec: Not a prop vector"

fromRVec :: RVec -> Res
fromRVec (RVec r) = Rename r

toRVec :: Res -> RVec
toRVec (Rename r) = RVec r
toRVec _          = error "toRVec: Not a rename vector"

fromDVec :: DVec -> Res
fromDVec (DVec n cs) = RDVec n cs

toDVec :: Res -> DVec
toDVec (RDVec n cs) = DVec n cs
toDVec _            = error "toDVec: Not a DVec"

refreshLyt :: VectorAlgebra a => (TopLayout DVec) -> G a (TopLayout DVec)
refreshLyt l@(InColumn _) = return l
refreshLyt (Nest (DVec n _) lyt) = do
    Just n' <- fromDict n
    lyt'    <- refreshLyt lyt
    return $ Nest (toDVec n') lyt'
refreshLyt (Pair l1 l2) = do
    l1' <- refreshLyt l1
    l2' <- refreshLyt l2
    return $ Pair l1' l2'

refreshShape :: VectorAlgebra a => (TopShape DVec) -> G a (TopShape DVec)
refreshShape (ValueVector (DVec n _) lyt) = do
    v <- fromDict n
    case v of
        Just n' -> do
            lyt' <- refreshLyt lyt
            return $ ValueVector (toDVec n') lyt'
        _ -> error $ "Disaster: " ++ show v
refreshShape (PrimVal (DVec n _) lyt) = do
    v <- fromDict n
    case v of
        Just (RDVec n' cs) -> do
            lyt'              <- refreshLyt lyt
            return $ PrimVal (DVec n' cs) lyt'
        x -> error $ show x

translate :: VectorAlgebra a => NodeMap V.VL -> AlgNode -> G a Res
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

vl2Algebra :: VectorAlgebra a => (NodeMap V.VL, TopShape DVec) -> G a (TopShape DVec)
vl2Algebra (vlNodes, plan) = do
    mapM_ (translate vlNodes) roots

    refreshShape plan
  where
    roots :: [AlgNode]
    roots = rootsFromTopShape plan

translateTerOp :: VectorAlgebra a => V.TerOp -> Res -> Res -> Res -> GraphM () a Res
translateTerOp t c1 c2 c3 =
    case t of
        V.Combine -> do
            (d, r1, r2) <- vecCombine (toDVec c1) (toDVec c2) (toDVec c3)
            return $ RTriple (fromDVec d) (fromRVec r1) (fromRVec r2)

translateBinOp :: VectorAlgebra a => V.BinOp -> Res -> Res -> GraphM () a Res
translateBinOp b c1 c2 = case b of
    V.GroupBy -> do
        (d, v, p) <- vecGroupBy (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec d) (fromDVec v) (fromPVec p)

    V.SortS -> do
        (d, p) <- vecSortS (toDVec c1) (toDVec c2)
        return $ RPair (fromDVec d) (fromPVec p)

    V.DistPrim -> do
        (v, p) <- vecDistPrim (toDVec c1) (toDVec c2)
        return $ RPair (fromDVec v) (fromPVec p)

    V.DistDesc -> do
        (v, p) <- vecDistDesc (toDVec c1) (toDVec c2)
        return $ RPair (fromDVec v) (fromPVec p)

    V.Align -> do
        (v, p) <- vecAlign (toDVec c1) (toDVec c2)
        return $ RPair (fromDVec v) (fromPVec p)

    V.PropRename -> fromDVec <$> vecPropRename (toRVec c1) (toDVec c2)

    V.PropFilter -> do
        (v, r) <- vecPropFilter (toRVec c1) (toDVec c2)
        return $ RPair (fromDVec v) (fromRVec r)

    V.PropReorder -> do
        (v, p) <- vecPropReorder (toPVec c1) (toDVec c2)
        return $ RPair (fromDVec v) (fromPVec p)

    V.Unbox -> do
        (v, r) <- vecUnbox (toRVec c1) (toDVec c2)
        return $ RPair (fromDVec v) (fromRVec r)

    V.Append -> do
        (v, r1, r2) <- vecAppend (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec v) (fromRVec r1) (fromRVec r2)

    V.AppendS -> do
        (v, r1, r2) <- vecAppendS (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec v) (fromRVec r1) (fromRVec r2)

    V.Restrict -> do
        (v, r) <- vecRestrict (toDVec c1) (toDVec c2)
        return $ RPair (fromDVec v) (fromRVec r)

    V.AggrS a -> fromDVec <$> vecAggrS a (toDVec c1) (toDVec c2)

    V.AggrNonEmptyS a -> fromDVec <$> vecAggrNonEmptyS a (toDVec c1) (toDVec c2)

    V.SelectPos o -> do
        (v, r, ru) <- vecSelectPos (toDVec c1) o (toDVec c2)
        return $ RTriple (fromDVec v) (fromRVec r) (fromRVec ru)

    V.SelectPosS o -> do
        (v, rp, ru) <- vecSelectPosS (toDVec c1) o (toDVec c2)
        return $ RTriple (fromDVec v) (fromRVec rp) (fromRVec ru)

    V.Zip -> fromDVec <$> vecZip (toDVec c1) (toDVec c2)

    V.ZipS -> do
        (v, r1 ,r2) <- vecZipS (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec v) (fromRVec r1) (fromRVec r2)

    V.CartProduct -> do
        (v, p1, p2) <- vecCartProduct (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec v) (fromPVec p1) (fromPVec p2)

    V.CartProductS -> do
        (v, p1, p2) <- vecCartProductS (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec v) (fromPVec p1) (fromPVec p2)

    V.NestProductS -> do
        (v, p2) <- vecNestProductS (toDVec c1) (toDVec c2)
        return $ RPair (fromDVec v) (fromPVec p2)

    V.ThetaJoin p -> do
        (v, p1, p2) <- vecThetaJoin p (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec v) (fromPVec p1) (fromPVec p2)

    V.ThetaJoinS p -> do
        (v, p1, p2) <- vecThetaJoinS p (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec v) (fromPVec p1) (fromPVec p2)

    V.NestJoinS p -> do
        (v, p2) <- vecNestJoinS p (toDVec c1) (toDVec c2)
        return $ RPair (fromDVec v) (fromPVec p2)

    V.SemiJoin p -> do
        (v, r) <- vecSemiJoin p (toDVec c1) (toDVec c2)
        return $ RPair (fromDVec v) (fromRVec r)

    V.SemiJoinS p -> do
        (v, r) <- vecSemiJoinS p (toDVec c1) (toDVec c2)
        return $ RPair (fromDVec v) (fromRVec r)

    V.AntiJoin p -> do
        (v, r) <- vecAntiJoin p (toDVec c1) (toDVec c2)
        return $ RPair (fromDVec v) (fromRVec r)

    V.AntiJoinS p -> do
        (v, r) <- vecAntiJoinS p (toDVec c1) (toDVec c2)
        return $ RPair (fromDVec v) (fromRVec r)

    V.TransposeS -> do
        (qo, qi) <- vecTransposeS (toDVec c1) (toDVec c2)
        return $ RPair (fromDVec qo) (fromDVec qi)

translateUnOp :: VectorAlgebra a => V.UnOp -> Res -> GraphM () a Res
translateUnOp unop c = case unop of
    V.UniqueS          -> fromDVec <$> vecUniqueS (toDVec c)
    V.Number           -> fromDVec <$> vecNumber (toDVec c)
    V.NumberS          -> fromDVec <$> vecNumberS (toDVec c)
    V.DescToRename     -> fromRVec <$> descToRename (toDVec c)
    V.Segment          -> fromDVec <$> vecSegment (toDVec c)
    V.Unsegment        -> fromDVec <$> vecUnsegment (toDVec c)
    V.Select e         -> fromDVec <$> vecSelect e (toDVec c)
    V.Aggr a           -> fromDVec <$> vecAggr a (toDVec c)
    V.AggrNonEmpty as  -> fromDVec <$> vecAggrNonEmpty as (toDVec c)
    V.SortScalarS es -> do
        (d, p) <- vecSortScalarS es (toDVec c)
        return $ RPair (fromDVec d) (fromPVec p)
    V.GroupScalarS es -> do
        (qo, qi, p) <- vecGroupScalarS es (toDVec c)
        return $ RTriple (fromDVec qo) (fromDVec qi) (fromPVec p)
    V.Project cols -> fromDVec <$> vecProject cols (toDVec c)
    V.Reverse      -> do
        (d, p) <- vecReverse (toDVec c)
        return $ RPair (fromDVec d) (fromPVec p)
    V.ReverseS      -> do
        (d, p) <- vecReverseS (toDVec c)
        return $ RPair (fromDVec d) (fromPVec p)
    V.SelectPos1 op pos -> do
        (d, p, u) <- vecSelectPos1 (toDVec c) op pos
        return $ RTriple (fromDVec d) (fromRVec p) (fromRVec u)
    V.SelectPos1S op pos -> do
        (d, p, u) <- vecSelectPos1S (toDVec c) op pos
        return $ RTriple (fromDVec d) (fromRVec p) (fromRVec u)
    V.GroupAggr g as -> fromDVec <$> vecGroupAggr g as (toDVec c)

    V.Reshape n -> do
        (qo, qi) <- vecReshape n (toDVec c)
        return $ RPair (fromDVec qo) (fromDVec qi)
    V.ReshapeS n -> do
        (qo, qi) <- vecReshapeS n (toDVec c)
        return $ RPair (fromDVec qo) (fromDVec qi)
    V.Transpose -> do
        (qo, qi) <- vecTranspose (toDVec c)
        return $ RPair (fromDVec qo) (fromDVec qi)
    V.R1            -> case c of
        (RPair c1 _)     -> return c1
        (RTriple c1 _ _) -> return c1
        _                -> error "R1: Not a tuple"
    V.R2            -> case c of
        (RPair _ c2)     -> return c2
        (RTriple _ c2 _) -> return c2
        _                -> error "R2: Not a tuple"
    V.R3            -> case c of
        (RTriple _ _ c3) -> return c3
        _                -> error "R3: Not a tuple"

translateNullary :: VectorAlgebra a => V.NullOp -> GraphM () a Res
translateNullary V.SingletonDescr      = fromDVec <$> singletonDescr
translateNullary (V.Lit _ tys vals)    = fromDVec <$> vecLit tys vals
translateNullary (V.TableRef n tys hs) = fromDVec <$> vecTableRef n tys hs

-- | Insert SerializeRel operators in TA.TableAlgebra plans to define
-- descr and order columns as well as the required payload columns.
-- FIXME: once we are a bit more flexible wrt surrogates, determine the
-- surrogate (i.e. descr) columns from information in DVec.
insertSerialize :: G TA.TableAlgebra (TopShape DVec) -> G TA.TableAlgebra (TopShape DVec)
insertSerialize g = g >>= traverseShape

  where
    traverseShape :: TopShape DVec -> G TA.TableAlgebra (TopShape DVec)
    traverseShape (ValueVector dvec lyt) = do
        mLyt' <- traverseLayout lyt
        case mLyt' of
            Just lyt' -> do
                dvec' <- insertOp dvec noDescr needAbsPos
                return $ ValueVector dvec' lyt'
            Nothing   -> do
                dvec' <- insertOp dvec noDescr needRelPos
                return $ ValueVector dvec' lyt

    traverseShape (PrimVal dvec lyt)     = do
        mLyt' <- traverseLayout lyt
        case mLyt' of
            Just lyt' -> do
                dvec' <- insertOp dvec noDescr needAbsPos
                return $ PrimVal dvec' lyt'
            Nothing   -> do
                dvec' <- insertOp dvec noDescr noPos
                return $ PrimVal dvec' lyt

    traverseLayout :: (TopLayout DVec) -> G TA.TableAlgebra (Maybe (TopLayout DVec))
    traverseLayout (InColumn _) = return Nothing
    traverseLayout (Pair lyt1 lyt2) = do
        mLyt1' <- traverseLayout lyt1
        mLyt2' <- traverseLayout lyt2
        case (mLyt1', mLyt2') of
            (Just lyt1', Just lyt2') -> return $ Just $ Pair lyt1' lyt2'
            (Just lyt1', Nothing)    -> return $ Just $ Pair lyt1' lyt2
            (Nothing, Just lyt2')    -> return $ Just $ Pair lyt1 lyt2'
            (Nothing, Nothing)       -> return Nothing
    traverseLayout (Nest dvec lyt) = do
        mLyt' <- traverseLayout lyt
        case mLyt' of
            Just lyt' -> do
                dvec' <- insertOp dvec needDescr needAbsPos
                return $ Just $ Nest dvec' lyt'
            Nothing   -> do
                dvec' <- insertOp dvec needDescr needRelPos
                return $ Just $ Nest dvec' lyt


    -- | Insert a Serialize node for the given vector
    insertOp :: DVec -> Maybe TA.DescrCol -> TA.SerializeOrder -> G TA.TableAlgebra DVec
    insertOp (DVec q cols) descr pos = do
        let cs = map (TA.PayloadCol . ("item" ++) . show) cols
            op = TA.Serialize (descr, pos, cs)

        qp   <- lift $ insertNode $ UnOp op q
        return $ DVec qp cols

    needDescr = Just (TA.DescrCol "descr")
    noDescr   = Nothing

    needAbsPos = TA.AbsPos "pos"
    needRelPos = TA.RelPos ["pos"]
    noPos      = TA.NoPos

implementVectorOpsX100 :: QueryPlan V.VL -> QueryPlan X100Algebra
implementVectorOpsX100 vlPlan = mkQueryPlan opMap shape tagMap
  where
    x100Plan               = vl2Algebra (nodeMap $ queryDag vlPlan, queryShape vlPlan)
    (opMap, shape, tagMap) = runG dummy x100Plan

implementVectorOpsPF :: QueryPlan V.VL -> QueryPlan TA.TableAlgebra
implementVectorOpsPF vlPlan = mkQueryPlan opMap shape tagMap
  where
    taPlan                 = vl2Algebra (nodeMap $ queryDag vlPlan, queryShape vlPlan)
    serializedPlan         = insertSerialize taPlan
    (opMap, shape, tagMap) = runG $unimplemented serializedPlan
