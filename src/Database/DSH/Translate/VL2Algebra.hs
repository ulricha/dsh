{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE FlexibleContexts #-}

module Database.DSH.Translate.VL2Algebra
    ( implementVectorOpsX100
    , implementVectorOpsPF
    ) where

import qualified Data.IntMap                          as IM
import           Data.List
import qualified Data.Map                             as M
import           Data.Maybe

import           Control.Applicative
import           Control.Monad.State

import qualified Database.Algebra.Dag                 as D
import qualified Database.Algebra.Dag.Build           as B
import           Database.Algebra.Dag.Common
import qualified Database.Algebra.Table.Lang          as TA
import           Database.Algebra.X100.Data           (X100Algebra)

import           Database.DSH.Impossible
import           Database.DSH.Common.QueryPlan
import           Database.DSH.Translate.FKL2VL        ()
import           Database.DSH.VL.Vector
import qualified Database.DSH.VL.Lang                 as V
import           Database.DSH.VL.VectorAlgebra
import           Database.DSH.VL.VectorAlgebra.TA     ()
import           Database.DSH.VL.VectorAlgebra.X100   ()

-- | A layer on top of the DAG builder monad that caches the
-- translation result of VL nodes.
type VecBuild a v = StateT (M.Map AlgNode (Res v)) (B.Build a)

runVecBuild :: VectorAlgebra v a => VecBuild a v r -> (D.AlgebraDag a, r, NodeMap [Tag])
runVecBuild c = B.runBuild $ fst <$> runStateT c M.empty

data Res v = Prop    AlgNode
           | Rename  AlgNode
           | RDVec   v
           | RLPair   (Res v) (Res v)
           | RTriple (Res v) (Res v) (Res v)
         deriving Show

fromDict :: VectorAlgebra v a => AlgNode -> VecBuild a v (Maybe (Res v))
fromDict n = do
    dict <- get
    return $ M.lookup n dict

insertTranslation :: VectorAlgebra v a => AlgNode -> Res v -> VecBuild a v ()
insertTranslation n res = modify (M.insert n res)

fromPVec :: PVec -> Res v
fromPVec (PVec p) = Prop p

toPVec :: Res v -> PVec
toPVec (Prop p) = PVec p
toPVec _       = error "toPVec: Not a prop vector"

fromRVec :: RVec -> Res v
fromRVec (RVec r) = Rename r

toRVec :: Res v -> RVec
toRVec (Rename r) = RVec r
toRVec _          = error "toRVec: Not a rename vector"

fromDVec :: v -> Res v
fromDVec v = RDVec v

toDVec :: Res v -> v
toDVec (RDVec v) = v
toDVec _         = error "toDVec: Not a NDVec"

refreshLyt :: VectorAlgebra v a => Layout VLDVec -> VecBuild a v (Layout v)
refreshLyt (LCol c) = return $ LCol c
refreshLyt (LNest (VLDVec n) lyt) = do
    Just n' <- fromDict n
    lyt'    <- refreshLyt lyt
    return $ LNest (toDVec n') lyt'
refreshLyt (LTuple lyts) = LTuple <$> mapM refreshLyt lyts

refreshShape :: VectorAlgebra v a => Shape VLDVec -> VecBuild a v (Shape v)
refreshShape (VShape (VLDVec n) lyt) = do
    mv <- fromDict n
    case mv of
        Just v -> do
            lyt' <- refreshLyt lyt
            return $ VShape (toDVec v) lyt'
        _ -> $impossible
refreshShape (SShape (VLDVec n) lyt) = do
    mv <- fromDict n
    case mv of
        Just (RDVec v) -> do
            lyt'              <- refreshLyt lyt
            return $ SShape v lyt'
        _ -> $impossible

translate :: VectorAlgebra v a => NodeMap V.VL -> AlgNode -> VecBuild a v (Res v)
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

vl2Algebra :: VectorAlgebra v a => NodeMap V.VL -> Shape VLDVec -> VecBuild a v (Shape v)
vl2Algebra vlNodes plan = do
    mapM_ (translate vlNodes) roots

    refreshShape plan
  where
    roots :: [AlgNode]
    roots = shapeNodes plan

translateTerOp :: VectorAlgebra v a => V.TerOp -> Res v -> Res v -> Res v -> B.Build a (Res v)
translateTerOp t c1 c2 c3 =
    case t of
        V.Combine -> do
            (d, r1, r2) <- vecCombine (toDVec c1) (toDVec c2) (toDVec c3)
            return $ RTriple (fromDVec d) (fromRVec r1) (fromRVec r2)

translateBinOp :: VectorAlgebra v a => V.BinOp -> Res v -> Res v -> B.Build a (Res v)
translateBinOp b c1 c2 = case b of
    V.Group -> do
        (d, v, p) <- vecGroup (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec d) (fromDVec v) (fromPVec p)

    V.DistPrim -> do
        (v, p) <- vecDistPrim (toDVec c1) (toDVec c2)
        return $ RLPair (fromDVec v) (fromPVec p)

    V.DistDesc -> do
        (v, p) <- vecDistDesc (toDVec c1) (toDVec c2)
        return $ RLPair (fromDVec v) (fromPVec p)

    V.DistLift -> do
        (v, p) <- vecDistLift (toDVec c1) (toDVec c2)
        return $ RLPair (fromDVec v) (fromPVec p)

    V.PropRename -> fromDVec <$> vecPropRename (toRVec c1) (toDVec c2)

    V.PropFilter -> do
        (v, r) <- vecPropFilter (toRVec c1) (toDVec c2)
        return $ RLPair (fromDVec v) (fromRVec r)

    V.PropReorder -> do
        (v, p) <- vecPropReorder (toPVec c1) (toDVec c2)
        return $ RLPair (fromDVec v) (fromPVec p)

    V.UnboxNested -> do
        (v, r) <- vecUnboxNested (toRVec c1) (toDVec c2)
        return $ RLPair (fromDVec v) (fromRVec r)

    V.UnboxScalar -> RDVec <$> vecUnboxScalar (toDVec c1) (toDVec c2)

    V.Append -> do
        (v, r1, r2) <- vecAppend (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec v) (fromRVec r1) (fromRVec r2)

    V.AppendS -> do
        (v, r1, r2) <- vecAppendS (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec v) (fromRVec r1) (fromRVec r2)

    V.AggrS a -> fromDVec <$> vecAggrS a (toDVec c1) (toDVec c2)


    V.SelectPos o -> do
        (v, r, ru) <- vecSelectPos (toDVec c1) o (toDVec c2)
        return $ RTriple (fromDVec v) (fromRVec r) (fromRVec ru)

    V.SelectPosS o -> do
        (v, rp, ru) <- vecSelectPosS (toDVec c1) o (toDVec c2)
        return $ RTriple (fromDVec v) (fromRVec rp) (fromRVec ru)

    V.Zip -> fromDVec <$> vecZip (toDVec c1) (toDVec c2)
    V.Align -> fromDVec <$> vecZip (toDVec c1) (toDVec c2)

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
        return $ RLPair (fromDVec v) (fromPVec p2)

    V.ThetaJoin p -> do
        (v, p1, p2) <- vecThetaJoin p (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec v) (fromPVec p1) (fromPVec p2)

    V.NestJoin p -> do
        (v, p1, p2) <- vecNestJoin p (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec v) (fromPVec p1) (fromPVec p2)

    V.ThetaJoinS p -> do
        (v, p1, p2) <- vecThetaJoinS p (toDVec c1) (toDVec c2)
        return $ RTriple (fromDVec v) (fromPVec p1) (fromPVec p2)

    V.NestJoinS p -> do
        (v, p2) <- vecNestJoinS p (toDVec c1) (toDVec c2)
        return $ RLPair (fromDVec v) (fromPVec p2)

    V.SemiJoin p -> do
        (v, r) <- vecSemiJoin p (toDVec c1) (toDVec c2)
        return $ RLPair (fromDVec v) (fromRVec r)

    V.SemiJoinS p -> do
        (v, r) <- vecSemiJoinS p (toDVec c1) (toDVec c2)
        return $ RLPair (fromDVec v) (fromRVec r)

    V.AntiJoin p -> do
        (v, r) <- vecAntiJoin p (toDVec c1) (toDVec c2)
        return $ RLPair (fromDVec v) (fromRVec r)

    V.AntiJoinS p -> do
        (v, r) <- vecAntiJoinS p (toDVec c1) (toDVec c2)
        return $ RLPair (fromDVec v) (fromRVec r)

    V.TransposeS -> do
        (qo, qi) <- vecTransposeS (toDVec c1) (toDVec c2)
        return $ RLPair (fromDVec qo) (fromDVec qi)

translateUnOp :: VectorAlgebra v a => V.UnOp -> Res v -> B.Build a (Res v)
translateUnOp unop c = case unop of
    V.AggrNonEmptyS a  -> fromDVec <$> vecAggrNonEmptyS a (toDVec c)
    V.UniqueS          -> fromDVec <$> vecUniqueS (toDVec c)
    V.Number           -> fromDVec <$> vecNumber (toDVec c)
    V.NumberS          -> fromDVec <$> vecNumberS (toDVec c)
    V.UnboxRename      -> fromRVec <$> descToRename (toDVec c)
    V.Segment          -> fromDVec <$> vecSegment (toDVec c)
    V.Unsegment        -> fromDVec <$> vecUnsegment (toDVec c)
    V.Aggr a           -> fromDVec <$> vecAggr a (toDVec c)
    V.WinFun  (a, w)   -> fromDVec <$> vecWinFun a w (toDVec c)
    V.AggrNonEmpty as  -> fromDVec <$> vecAggrNonEmpty as (toDVec c)
    V.Select e         -> do
        (d, r) <- vecSelect e (toDVec c)
        return $ RLPair (fromDVec d) (fromRVec r)
    V.SortS es         -> do
        (d, p) <- vecSortS es (toDVec c)
        return $ RLPair (fromDVec d) (fromPVec p)
    V.GroupScalarS es -> do
        (qo, qi, p) <- vecGroupScalarS es (toDVec c)
        return $ RTriple (fromDVec qo) (fromDVec qi) (fromPVec p)
    V.Project cols -> fromDVec <$> vecProject cols (toDVec c)
    V.Reverse      -> do
        (d, p) <- vecReverse (toDVec c)
        return $ RLPair (fromDVec d) (fromPVec p)
    V.ReverseS      -> do
        (d, p) <- vecReverseS (toDVec c)
        return $ RLPair (fromDVec d) (fromPVec p)
    V.SelectPos1 (op, pos) -> do
        (d, p, u) <- vecSelectPos1 (toDVec c) op pos
        return $ RTriple (fromDVec d) (fromRVec p) (fromRVec u)
    V.SelectPos1S (op, pos) -> do
        (d, p, u) <- vecSelectPos1S (toDVec c) op pos
        return $ RTriple (fromDVec d) (fromRVec p) (fromRVec u)
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

translateNullary :: VectorAlgebra v a => V.NullOp -> B.Build a (Res v)
translateNullary V.SingletonDescr          = fromDVec <$> singletonDescr
translateNullary (V.Lit (_, tys, vals))    = fromDVec <$> vecLit tys vals
translateNullary (V.TableRef (n, tys, hs)) = fromDVec <$> vecTableRef n tys hs

-- | Insert SerializeRel operators in TA.TableAlgebra plans to define
-- descr and order columns as well as the required payload columns.
-- FIXME: once we are a bit more flexible wrt surrogates, determine the
-- surrogate (i.e. descr) columns from information in NDVec.
insertSerialize :: VecBuild TA.TableAlgebra NDVec (Shape NDVec) 
                -> VecBuild TA.TableAlgebra NDVec (Shape NDVec)
insertSerialize g = g >>= traverseShape

  where
    traverseShape :: Shape NDVec -> VecBuild TA.TableAlgebra NDVec (Shape NDVec)
    traverseShape (VShape dvec lyt) = do
        mLyt' <- traverseLayout lyt
        case mLyt' of
            Just lyt' -> do
                dvec' <- insertOp dvec noDescr needAbsPos
                return $ VShape dvec' lyt'
            Nothing   -> do
                dvec' <- insertOp dvec noDescr needRelPos
                return $ VShape dvec' lyt

    traverseShape (SShape dvec lyt)     = do
        mLyt' <- traverseLayout lyt
        case mLyt' of
            Just lyt' -> do
                dvec' <- insertOp dvec noDescr needAbsPos
                return $ SShape dvec' lyt'
            Nothing   -> do
                dvec' <- insertOp dvec noDescr noPos
                return $ SShape dvec' lyt

    traverseLayout :: (Layout NDVec) -> VecBuild TA.TableAlgebra NDVec (Maybe (Layout NDVec))
    traverseLayout (LCol _) = return Nothing
    traverseLayout (LTuple lyts) = do
        mLyts <- mapM traverseLayout lyts
        if all isNothing mLyts
            then return Nothing
            else return $ Just $ LTuple $ zipWith (\l ml -> maybe l id ml) lyts mLyts
    traverseLayout (LNest dvec lyt) = do
        mLyt' <- traverseLayout lyt
        case mLyt' of
            Just lyt' -> do
                dvec' <- insertOp dvec needDescr needAbsPos
                return $ Just $ LNest dvec' lyt'
            Nothing   -> do
                dvec' <- insertOp dvec needDescr needRelPos
                return $ Just $ LNest dvec' lyt


    -- | Insert a Serialize node for the given vector
    insertOp :: NDVec -> Maybe TA.DescrCol -> TA.SerializeOrder -> VecBuild TA.TableAlgebra NDVec NDVec
    insertOp (ADVec q cols) descr pos = do
        let cs = map (TA.PayloadCol . ("item" ++) . show) cols
            op = TA.Serialize (descr, pos, cs)

        qp   <- lift $ B.insert $ UnOp op q
        return $ ADVec qp cols

    needDescr = Just (TA.DescrCol "descr")
    noDescr   = Nothing

    needAbsPos = TA.AbsPos "pos"
    needRelPos = TA.RelPos ["pos"]
    noPos      = TA.NoPos

implementVectorOpsX100 :: QueryPlan V.VL VLDVec -> QueryPlan X100Algebra NDVec
implementVectorOpsX100 vlPlan = mkQueryPlan dag shape tagMap
  where
    x100Plan             = vl2Algebra (D.nodeMap $ queryDag vlPlan) (queryShape vlPlan)
    (dag, shape, tagMap) = runVecBuild x100Plan

implementVectorOpsPF :: QueryPlan V.VL VLDVec -> QueryPlan TA.TableAlgebra NDVec
implementVectorOpsPF vlPlan = mkQueryPlan dag shape tagMap
  where
    taPlan               = vl2Algebra (D.nodeMap $ queryDag vlPlan) (queryShape vlPlan)
    serializedPlan       = insertSerialize taPlan
    (dag, shape, tagMap) = runVecBuild serializedPlan
