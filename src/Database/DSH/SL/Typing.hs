{-# LANGUAGE FlexibleContexts #-}

module Database.DSH.SL.Typing
    ( inferSLTypes
    ) where

import           Control.Monad.Except
import           Control.Monad.Reader
import           Data.List
import           Text.PrettyPrint.ANSI.Leijen                  hiding ((<$>))
import qualified Text.PrettyPrint.ANSI.Leijen                  as P
import           Text.Printf
import           Data.List.NonEmpty(NonEmpty((:|)))
import qualified Data.IntMap                                   as IM

import           Database.Algebra.Dag.Common
import           Database.Algebra.Dag

import qualified Database.DSH.Common.Lang as L
import           Database.DSH.Common.Pretty                    hiding (join)
import           Database.DSH.Common.Type
import           Database.DSH.Common.Opt
import qualified Database.DSH.Common.VectorLang as VL

import           Database.DSH.SL.Lang

--------------------------------------------------------------------------------
-- Typing Helpers

-- | Type errors for MA operators
tyErr :: (MonadError String m, Pretty o) => String -> o -> [VL.PType] -> m a
tyErr op arg csTys = throwError $ printf "%s{%s} %s" op (pp arg) (concat $ intersperse " " (map pp csTys))

pPairT :: VL.PType -> VL.PType -> VL.PType
pPairT ty1 ty2 = VL.PTupleT $ ty1 :| pure ty2

-- | Typecheck a tuple expression with the given input type
expTy :: MonadError String m => VL.PType -> VL.TExpr -> m VL.PType
expTy ty e = runReaderT (VL.tExpTy e) (Just ty)

-- | Typecheck a *constant* tuple expression
constEnvTy :: MonadError String m => VL.TExpr -> m VL.PType
constEnvTy e = runReaderT (VL.tExpTy e) Nothing

-- | Typecheck an aggregate function with the given input type
aggrTy :: MonadError String m => VL.PType -> VL.AggrFun VL.TExpr -> m VL.PType
aggrTy ty a = runReaderT (VL.tAggrTy a) (Just ty)

-- | Typecheck a window function with the given input type
winTy :: MonadError String m => VL.PType -> VL.WinFun VL.TExpr -> m VL.PType
winTy ty a = runReaderT (VL.tWinTy a) (Just ty)

--------------------------------------------------------------------------------
-- Typing of operators

data VecTup = T1 VecTy
            | T2 VecTy VecTy
            | T3 VecTy VecTy VecTy

data VecTy = DVec VL.PType
           | RVec
           | KVec
           | FVec
           | SVec

instance Pretty VecTy where
    pretty (DVec ty) = char 'D' P.<> parens (pretty ty)
    pretty RVec = char 'R'
    pretty KVec = char 'K'
    pretty FVec = char 'F'
    pretty SVec = char 'S'

instance Pretty VecTup where
    pretty (T1 ty)          = pretty ty
    pretty (T2 ty1 ty2)     = pretty (ty1, ty2)
    pretty (T3 ty1 ty2 ty3) = pretty (ty1, ty2, ty3)

vecTy :: MonadError String m => VecTup -> m VecTy
vecTy (T1 ty) = pure ty
vecTy t       = throwError $ printf "vecTy: not a single vector: %s" (pp t)

plTy :: MonadError String m => VecTy -> m VL.PType
plTy (DVec ty) = pure ty
plTy vTy       = throwError $ printf "plTy: not a data vector: %s" (pp vTy)

-- | Typing of unary SL operators
tyUnOp :: MonadError String m => VecTup -> UnOp VL.TExpr VL.TExpr -> m VecTup
tyUnOp t R1          =
    case t of
        T1 vTy     -> pure $ T1 vTy
        T2 vTy _   -> pure $ T1 vTy
        T3 vTy _ _ -> pure $ T1 vTy
tyUnOp t R2          =
    case t of
        T1 _       -> throwError $ printf "not a vector pair: %s" (pp t)
        T2 _ vTy   -> pure $ T1 vTy
        T3 _ vTy _ -> pure $ T1 vTy
tyUnOp t R3          =
    case t of
        T1 _       -> throwError $ printf "not a vector triple: %s" (pp t)
        T2 _ _     -> throwError $ printf "not a vector triple: %s" (pp t)
        T3 _ _ vTy -> pure $ T1 vTy
tyUnOp t (Project e) = vecTy t >>= plTy >>= \ty -> T1 <$> DVec <$> expTy ty e
tyUnOp t (Select e)  = do
    ty     <- vecTy t >>= plTy
    predTy <- expTy ty e
    case predTy of
        VL.PScalarT BoolT -> pure $ T2 (DVec ty) FVec
        _                 -> tyErr "select" e [ty]
tyUnOp t Segment     = vecTy t >>= plTy >>= \ty -> pure $ T1 $ DVec ty
tyUnOp t Unique      = vecTy t >>= plTy >>= \ty -> pure $ T1 $ DVec ty
tyUnOp t Reverse     = vecTy t >>= plTy >>= \ty -> pure $ T1 $ DVec ty
tyUnOp t Unsegment   = vecTy t >>= plTy >>= \ty -> pure $ T1 $ DVec ty
tyUnOp t Number      = do
    ty <- vecTy t >>= plTy
    pure $ T1 $ DVec $ pPairT ty (VL.PScalarT IntT)
tyUnOp t (Sort e)    = do
    ty <- vecTy t >>= plTy
    _  <- expTy ty e
    pure $ T2 (DVec ty) SVec
tyUnOp t (Group e)   = do
    ty  <- vecTy t >>= plTy
    gTy <- expTy ty e
    pure $ T3 (DVec gTy) (DVec ty) SVec
tyUnOp t (WinFun (w, _)) = do
    ty <- vecTy t >>= plTy
    wTy <- winTy ty w
    pure $ T1 $ DVec $ pPairT ty wTy
tyUnOp t (GroupAggr (e, as)) = do
    ty   <- vecTy t >>= plTy
    gTy  <- expTy ty e
    aTys <- sequenceA $ fmap (aggrTy ty) $ L.getNE as
    case aTys of
        aTy :| [] -> pure $ T1 $ DVec $ pPairT gTy aTy
        _ :| _    -> pure $ T1 $ DVec $ pPairT gTy (VL.PTupleT aTys)
tyUnOp t (Fold a) = do
    ty  <- vecTy t >>= plTy
    aTy <- aggrTy ty a
    pure $ T1 $ DVec aTy

-- | Typing of binary SL operators
tyBinOp :: MonadError String m => VecTup -> VecTup -> BinOp VL.TExpr -> m VecTup
tyBinOp t1 t2 ReplicateNest = do
    ty1 <- vecTy t1 >>= plTy
    ty2 <- vecTy t2 >>= plTy
    pure $ T2 (DVec $ pPairT ty1 ty2) RVec
tyBinOp t1 t2 ReplicateScalar = do
    ty1 <- vecTy t1 >>= plTy
    ty2 <- vecTy t2 >>= plTy
    pure $ T2 (DVec $ pPairT ty1 ty2) RVec
tyBinOp t1 t2 ReplicateVector = do
    ty1 <- vecTy t1 >>= plTy
    _   <- vecTy t2 >>= plTy
    pure $ T2 (DVec ty1) RVec
tyBinOp t1 t2 AppKey = do
    KVec <- vecTy t1
    ty   <- vecTy t2 >>= plTy
    pure $ T1 (DVec ty)
tyBinOp t1 t2 AppRep = do
    RVec <- vecTy t1
    ty   <- vecTy t2 >>= plTy
    pure $ T2 (DVec ty) RVec
tyBinOp t1 t2 AppSort = do
    SVec <- vecTy t1
    ty   <- vecTy t2 >>= plTy
    pure $ T2 (DVec ty) SVec
tyBinOp t1 t2 AppFilter = do
    FVec <- vecTy t1
    ty   <- vecTy t2 >>= plTy
    pure $ T2 (DVec ty) FVec
tyBinOp t1 t2 MergeSeg = do
    _   <- vecTy t1 >>= plTy
    ty2 <- vecTy t2 >>= plTy
    pure $ T1 $ DVec ty2
tyBinOp t1 t2 UnboxSng = do
    ty1 <- vecTy t1 >>= plTy
    ty2 <- vecTy t2 >>= plTy
    pure $ T2 (DVec $ pPairT ty1 ty2) KVec
tyBinOp t1 t2 (UnboxDefault e) = do
    ty1 <- vecTy t1 >>= plTy
    ty2 <- vecTy t2 >>= plTy
    dTy <- constEnvTy e
    if dTy == ty2
        then pure $ T1 $ DVec $ pPairT ty1 ty2
        else tyErr "unboxdefault" e [ty1, ty2]
tyBinOp t1 t2 Align = do
    ty1 <- vecTy t1 >>= plTy
    ty2 <- vecTy t2 >>= plTy
    pure $ T1 $ DVec $ pPairT ty1 ty2
tyBinOp t1 t2 Append = do
    ty1 <- vecTy t1 >>= plTy
    ty2 <- vecTy t2 >>= plTy
    if ty1 == ty2
        then pure $ T3 (DVec ty1) KVec KVec
        else tyErr "append" () [ty1, ty2]
tyBinOp t1 t2 Zip = do
    ty1 <- vecTy t1 >>= plTy
    ty2 <- vecTy t2 >>= plTy
    pure $ T3 (DVec $ pPairT ty1 ty2) RVec RVec
tyBinOp t1 t2 CartProduct = do
    ty1 <- vecTy t1 >>= plTy
    ty2 <- vecTy t2 >>= plTy
    pure $ T3 (DVec $ pPairT ty1 ty2) RVec RVec
tyBinOp t1 t2 (ThetaJoin p) = do
    ty1 <- vecTy t1 >>= plTy
    ty2 <- vecTy t2 >>= plTy
    VL.predTy ty1 ty2 p
    pure $ T3 (DVec $ pPairT ty1 ty2) RVec RVec
tyBinOp t1 t2 (SemiJoin p) = do
    ty1 <- vecTy t1 >>= plTy
    ty2 <- vecTy t2 >>= plTy
    VL.predTy ty1 ty2 p
    pure $ T2 (DVec ty1) FVec
tyBinOp t1 t2 (AntiJoin p) = do
    ty1 <- vecTy t1 >>= plTy
    ty2 <- vecTy t2 >>= plTy
    VL.predTy ty1 ty2 p
    pure $ T2 (DVec ty1) FVec
tyBinOp t1 t2 (NestJoin p) = do
    ty1 <- vecTy t1 >>= plTy
    ty2 <- vecTy t2 >>= plTy
    VL.predTy ty1 ty2 p
    pure $ T3 (DVec $ pPairT ty1 ty2) RVec RVec
tyBinOp t1 t2 (GroupJoin (p, as)) = do
    ty1 <- vecTy t1 >>= plTy
    ty2 <- vecTy t2 >>= plTy
    VL.predTy ty1 ty2 p
    aTys <- sequenceA $ fmap (aggrTy (pPairT ty1 ty2)) $ L.getNE as
    case aTys of
        aTy :| [] -> pure $ T1 $ DVec $ pPairT ty1 aTy
        _ :| _    -> pure $ T1 $ DVec $ pPairT ty1 (VL.PTupleT aTys)

-- | Typing of ternary SL operators
tyTerOp :: MonadError String m => VecTup -> VecTup -> VecTup -> TerOp -> m VecTup
tyTerOp t1 t2 t3 Combine = do
    ty1 <- vecTy t1 >>= plTy
    ty2 <- vecTy t2 >>= plTy
    ty3 <- vecTy t3 >>= plTy
    unless (ty1 == VL.PScalarT BoolT) $ tyErr "combine" () [ty1, ty2, ty3]
    unless (ty2 == ty3) $ tyErr "combine" () [ty1, ty2, ty3]
    pure $ T3 (DVec ty2) KVec KVec

-- | Typing of nullary SL operators
tyNullOp :: MonadError String m => NullOp -> m VecTup
tyNullOp (TableRef (_, schema)) = do
    let tupTy = VL.PTupleT $ fmap (VL.PScalarT . snd) $ L.tableCols schema
    pure $ T1 $ DVec tupTy
tyNullOp (Lit (ty, segs))     = do
    let es = case segs of
                 VL.UnitSeg s -> s
                 VL.Segs ss   -> join ss
    eTys <- sequenceA $ fmap (constEnvTy . VL.valExpr) es
    if all (== ty) eTys
        then pure $ T1 $ DVec ty
        else tyErr "lit" (ty, es) []

--------------------------------------------------------------------------------
-- Typing of SL DAGs

-- | Infer a type for all operators in an MA Dag.
inferSLTypes :: MonadError String m => AlgebraDag TSL -> m (NodeMap VecTup)
inferSLTypes = inferBottomUpE tyOp

childTy :: MonadError String m => AlgNode -> NodeMap VecTup -> m VecTup
childTy n m =
    case IM.lookup n m of
        Just ty -> pure ty
        Nothing -> throwError $ printf "No type for node %d" n

enrichTyErr :: MonadError String m => m a -> AlgNode -> [VecTup] -> m a
enrichTyErr ma n csTys = catchError ma $ \msg ->
    throwError $ printf "SL type inference failed at node %d\n%s\nmessage: %s" n csTyMsg msg
  where
    csTyMsg = concat $ intersperse "\n" $ map pp csTys

tyOp :: MonadError String m => NodeMap TSL -> TSL -> AlgNode -> NodeMap VecTup -> m VecTup
tyOp _ op n tyMap =
    case unSL op of
        BinOp o c1 c2  -> do
            t1 <- childTy c1 tyMap
            t2 <- childTy c2 tyMap
            enrichTyErr (tyBinOp t1 t2 o) n [t1, t2]
        (UnOp o c) -> do
            t <- childTy c tyMap
            enrichTyErr (tyUnOp t o) n [t]
        (NullaryOp o) -> enrichTyErr (tyNullOp o) n []
        (TerOp o c1 c2 c3) -> do
            t1 <- childTy c1 tyMap
            t2 <- childTy c2 tyMap
            t3 <- childTy c3 tyMap
            enrichTyErr (tyTerOp t1 t2 t3 o) n [t1, t2, t3]
