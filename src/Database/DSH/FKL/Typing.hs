{-# LANGUAGE FlexibleContexts #-}

-- | Type checking for FKL expressions
module Database.DSH.FKL.Typing
    ( inferFKLTy
    ) where

import           Control.Monad.Except
import           Control.Monad.Reader
import           Data.List
import qualified Data.List.NonEmpty         as N
import           Text.Printf

import           Database.DSH.FKL.Lang
import           Database.DSH.Common.Lang
import           Database.DSH.Common.Type
import           Database.DSH.Common.Pretty
import           Database.DSH.Common.Nat

--------------------------------------------------------------------------------
-- Typing infrastructure

type TyEnv = [(Ident, Type)]

expTyErr :: FExpr -> String -> Typing a
expTyErr a msg = throwError $ printf "FKL type inference failed in expression\n>>>\n%s\n<<<\n\n%s" (pp a) msg

opTyErr :: String -> [Type] -> Typing a
opTyErr msg tys = throwError $ printf "FKL type error: %s {%s}" msg tyMsg
  where
    tyMsg = concat $ intersperse "," $ fmap pp tys

bindTy :: Ident -> Type -> TyEnv -> TyEnv
bindTy x ty tyEnv = (x,ty) : tyEnv

lookupTy :: Ident -> Typing Type
lookupTy x = do
    tyEnv <- ask
    case lookup x tyEnv of
        Just ty -> pure ty
        Nothing -> throwError $ printf "FKL type error: %s not in type env %s" x (pp tyEnv)

type Typing = ReaderT TyEnv (Either String)

--------------------------------------------------------------------------------
-- Monad type predicates

elemTy :: Type -> Typing Type
elemTy (ListT ty) = pure ty
elemTy ty         = throwError $ printf "FKL type error: %s not a list type" (pp ty)

listTy :: Type -> Typing ()
listTy (ListT _) = pure ()
listTy ty        = throwError $ printf "FKL type error: %s not a list type" (pp ty)

numTy :: Type -> Typing ()
numTy (ScalarT IntT)     = pure ()
numTy (ScalarT DoubleT)  = pure ()
numTy (ScalarT DecimalT) = pure ()
numTy ty                 = throwError $ printf "FKL type error: %s not a numeric type" (pp ty)

boolTy :: Type -> Typing ()
boolTy (ScalarT BoolT) = pure ()
boolTy ty              = throwError $ printf "FKL type error: %s not boolean" (pp ty)

fractTy :: Type -> Typing ()
fractTy (ScalarT DoubleT)  = pure ()
fractTy (ScalarT DecimalT) = pure ()
fractTy ty                 = throwError $ printf "FKL type error: %s not a fractional type" (pp ty)

scalarTy :: Type -> Typing ScalarType
scalarTy (ScalarT sty) = pure sty
scalarTy ty            = throwError $ printf "FKL type error: %s not a scalar type" (pp ty)

--------------------------------------------------------------------------------
-- Type inference

-- | Typing of unary builtins
tyPrim1 :: Prim1 -> Type -> Typing Type
tyPrim1 Singleton ty   = pure $ ListT ty
tyPrim1 Only ty        = catchError (elemTy ty) (const $ opTyErr "only" [ty])
tyPrim1 Concat ty      =
    case ty of
        ListT (ListT eTy) -> pure $ ListT eTy
        _                 -> opTyErr "concat" [ty]
tyPrim1 Reverse ty     = catchError (listTy ty) (const $ opTyErr "reverse" [ty]) >> pure ty
tyPrim1 Nub ty         = catchError (listTy ty) (const $ opTyErr "nub" [ty]) >> pure ty
tyPrim1 Number ty      = flip catchError (const $ opTyErr "number" [ty]) $ do
    eTy <- elemTy ty
    pure $ ListT $ TupleT [eTy, ScalarT IntT]
tyPrim1 Sort ty        = do
    case ty of
        ListT (TupleT [ty1, _]) -> pure $ ListT ty1
        _                       -> opTyErr "sort" [ty]
tyPrim1 Group ty       = do
    case ty of
        ListT (TupleT [ty1, ty2]) -> pure $ ListT (TupleT [ty2, ListT ty1])
        _                         -> opTyErr "group" [ty]
tyPrim1 (TupElem i) ty =
    case ty of
        TupleT tys -> maybe (opTyErr (printf "_.%d" (tupleIndex i)) [ty])
                            pure
                            (safeIndex i tys)
        _          -> opTyErr (printf "_.%d" (tupleIndex i)) [ty]
tyPrim1 (Agg a) ty     = flip catchError (const $ opTyErr (pp a) [ty]) $ do
    eTy <- elemTy ty
    case a of
        Length  -> pure $ ScalarT IntT
        Sum     -> numTy eTy >> pure eTy
        Avg     -> fractTy eTy >> pure eTy
        And     -> boolTy eTy >> pure eTy
        Or      -> boolTy eTy >> pure eTy
        Maximum -> void (scalarTy eTy) >> pure eTy
        Minimum -> void (scalarTy eTy) >> pure eTy
tyPrim1 Restrict ty    =
    case ty of
        ListT (TupleT [ty1, ScalarT BoolT]) -> pure $ ListT ty1
        _                                   -> opTyErr "restrict" [ty]

-- | Typing of binary builtins
tyPrim2 :: Prim2 -> Type -> Type -> Typing Type
tyPrim2 Append ty1 ty2           =
    if isList ty1 && isList ty2 && ty1 == ty2
    then pure ty1
    else opTyErr "append" [ty1, ty2]
tyPrim2 Zip ty1 ty2              = flip catchError (const $ opTyErr "zip" [ty1,ty2]) $ do
    ety1 <- elemTy ty1
    ety2 <- elemTy ty2
    pure $ ListT $ TupleT [ety1, ety2]
tyPrim2 CartProduct ty1 ty2      = flip catchError (const $ opTyErr "cartproduct" [ty1,ty2]) $ do
    ety1 <- elemTy ty1
    ety2 <- elemTy ty2
    pure $ ListT $ TupleT [ety1, ety2]
tyPrim2 (ThetaJoin p) ty1 ty2    = flip catchError (const $ opTyErr "thetajoin" [ty1,ty2]) $ do
    ety1 <- elemTy ty1
    ety2 <- elemTy ty2
    checkPredTy ety1 ety2 p
    pure $ ListT $ TupleT [ety1, ety2]
tyPrim2 (NestJoin p) ty1 ty2     = flip catchError (const $ opTyErr "nestjoin" [ty1, ty2]) $ do
    ety1 <- elemTy ty1
    ety2 <- elemTy ty2
    checkPredTy ety1 ety2 p
    pure $ ListT $ TupleT [ety1, ListT (TupleT [ety1, ety2])]
tyPrim2 (SemiJoin p) ty1 ty2     = flip catchError (const $ opTyErr "semijoin" [ty1, ty2]) $ do
    ety1 <- elemTy ty1
    ety2 <- elemTy ty2
    checkPredTy ety1 ety2 p
    pure $ ListT ety1
tyPrim2 (AntiJoin p) ty1 ty2     = flip catchError (const $ opTyErr "antijoin" [ty1, ty2]) $ do
    ety1 <- elemTy ty1
    ety2 <- elemTy ty2
    checkPredTy ety1 ety2 p
    pure $ ListT ety1
tyPrim2 (GroupJoin p as) ty1 ty2 = flip catchError (const $ opTyErr "groupjoin" [ty1, ty2]) $ do
    ety1 <- elemTy ty1
    ety2 <- elemTy ty2
    checkPredTy ety1 ety2 p
    aTys <- runReaderT (mapM aggrTy $ N.toList $ getNE as) (Just $ TupleT [ety1, ety2])
    case aTys of
        [aTy] -> pure $ ListT $ TupleT [ety1, aTy]
        _     -> pure $ ListT $ TupleT [ety1, TupleT aTys]
tyPrim2 Dist ty1 ty2             = flip catchError (const $ opTyErr "dist" [ty1, ty2]) $ do
    if isList ty2
       then pure $ ListT ty1
       else throwError "FKL.Typing.dist: not a list"

tyPrim3 :: Prim3 -> Type -> Type -> Type -> Typing Type
tyPrim3 Combine ty1 ty2 ty3 = flip catchError (const $ opTyErr "combine" [ty1, ty2, ty3]) $ do
    eTy1 <- elemTy ty1
    eTy2 <- elemTy ty2
    eTy3 <- elemTy ty3
    if eTy1 == ScalarT BoolT && eTy2 == eTy3
       then pure $ ListT eTy2
       else throwError "FKL.Typing.combine: type error"

tyPrim3Lift :: Lifted -> Prim3 -> Type -> Type -> Type -> Typing Type
tyPrim3Lift Lifted p ty1 ty2 ty3    = do
    eTy1 <- elemTy ty1
    eTy2 <- elemTy ty2
    eTy3 <- elemTy ty3
    ListT <$> tyPrim3 p eTy1 eTy2 eTy3
tyPrim3Lift NotLifted p ty1 ty2 ty3 = tyPrim3 p ty1 ty2 ty3

tyPrim2Lift :: Lifted -> Prim2 -> Type -> Type -> Typing Type
tyPrim2Lift Lifted p ty1 ty2    = do
    eTy1 <- elemTy ty1
    eTy2 <- elemTy ty2
    ListT <$> tyPrim2 p eTy1 eTy2
tyPrim2Lift NotLifted p ty1 ty2 = tyPrim2 p ty1 ty2

tyPrim1Lift :: Lifted -> Prim1 -> Type -> Typing Type
tyPrim1Lift Lifted    p ty = do
    eTy <- elemTy ty
    ListT <$> tyPrim1 p eTy
tyPrim1Lift NotLifted p ty = tyPrim1 p ty

tyMkTuple :: Type -> Lifted -> [FExpr] -> Typing Type
tyMkTuple _     NotLifted es = TupleT <$> mapM inferTy es
tyMkTuple tyAnn Lifted    es = flip catchError (expTyErr $ MkTuple tyAnn Lifted es) $ do
    eTys <- mapM (\e -> inferTy e >>= elemTy) es
    pure $ ListT $ TupleT eTys

tyBinOpLift :: Lifted -> ScalarBinOp -> Type -> Type -> Typing Type
tyBinOpLift NotLifted o ty1 ty2 =
    case (ty1, ty2) of
        (ScalarT sTy1, ScalarT sTy2) -> ScalarT <$> inferBinOpScalar sTy1 sTy2 o
        _                            -> opTyErr (pp o) [ty1, ty2]
tyBinOpLift Lifted    o ty1 ty2 = do
    eTy1 <- elemTy ty1
    eTy2 <- elemTy ty2
    case (eTy1, eTy2) of
        (ScalarT sTy1, ScalarT sTy2) -> ListT <$> ScalarT <$> inferBinOpScalar sTy1 sTy2 o
        _                            -> opTyErr (pp o) [ty1, ty2]

tyUnOpLift :: Lifted -> ScalarUnOp -> Type -> Typing Type
tyUnOpLift NotLifted o ty =
    case ty of
        ScalarT sTy -> ScalarT <$> inferUnOpScalar sTy o
        _           -> opTyErr (pp o) [ty]
tyUnOpLift Lifted    o ty = do
    eTy <- elemTy ty
    case eTy of
        ScalarT sTy -> ListT <$> ScalarT <$> inferUnOpScalar sTy o
        _           -> opTyErr (pp o) [ty]

unwrapListType :: Nat -> Type -> Typing Type
unwrapListType Zero t               = pure t
unwrapListType (Succ n') (ListT xt) = unwrapListType n' xt
unwrapListType _         _          = throwError "NKL.Typing.forget"

wrapListType :: Nat -> Type -> Type
wrapListType Zero t     = t
wrapListType (Succ n') t = wrapListType n' (ListT t)

tyShapeExt :: ShapeExt -> Typing Type
tyShapeExt s@(Rep ty _ e)        = catchError (void (inferTy e) >> pure ty) (expTyErr $ Ext s)
tyShapeExt s@(Forget n _ e)      = catchError (inferTy e >>= unwrapListType n) (expTyErr $ Ext s)
tyShapeExt s@(Imprint n _ e1 e2) = flip catchError (expTyErr $ Ext s) $ do
    ty1 <- inferTy e1
    ty2 <- inferTy e2
    void $ unwrapListType n ty1
    pure $ wrapListType n ty2

-- | Typing of FKL expressions
inferTy :: FExpr -> Typing Type
inferTy (Table _ _ schema)     =
    pure $ ListT $ TupleT $ N.toList $ fmap (ScalarT . snd) $ tableCols schema
inferTy a@(PApp1 _ p l e)      = catchError (inferTy e >>= tyPrim1Lift l p) (expTyErr a)
inferTy a@(PApp2 _ p l e1 e2)  = do
    ty1 <- inferTy e1
    ty2 <- inferTy e2
    catchError (tyPrim2Lift l p ty1 ty2) (expTyErr a)
inferTy a@(PApp3 _ p l e1 e2 e3) = do
    ty1 <- inferTy e1
    ty2 <- inferTy e2
    ty3 <- inferTy e3
    catchError (tyPrim3Lift l p ty1 ty2 ty3) (expTyErr a)
inferTy a@(BinOp _ o l e1 e2)  = do
    ty1 <- inferTy e1
    ty2 <- inferTy e2
    catchError (tyBinOpLift l o ty1 ty2) (expTyErr a)
inferTy a@(UnOp _ o l e)       = do
    ty <- inferTy e
    catchError (tyUnOpLift l o ty) (expTyErr a)
inferTy (Const ty _)           = pure ty
inferTy (Var _ x)              = lookupTy x
inferTy (MkTuple ty l es)      = tyMkTuple ty l es
inferTy (Let _ x e1 e2)        = do
    ty1 <- inferTy e1
    local (bindTy x ty1) $ inferTy e2
inferTy (Ext e)                = tyShapeExt e

-- | Infer the type of a FKL expression
inferFKLTy :: FExpr -> Either String Type
inferFKLTy e = runReaderT (inferTy e) []
