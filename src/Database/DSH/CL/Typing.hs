{-# LANGUAGE FlexibleContexts #-}

-- | Type checking for CL expressions
module Database.DSH.CL.Typing
    ( inferCLTy
    ) where

import           Control.Monad.Except
import           Control.Monad.Reader
import           Data.List
import qualified Data.List.NonEmpty         as N
import           Text.Printf

import           Database.DSH.CL.Lang
import           Database.DSH.Common.Lang
import           Database.DSH.Common.Pretty
import           Database.DSH.Common.Nat

--------------------------------------------------------------------------------
-- Typing infrastructure

type TyEnv = [(Ident, Type)]

expTyErr :: Pretty e => e -> String -> Typing a
expTyErr a msg = throwError $ printf "CL type inference failed in expression\n>>>\n%s\n<<<\n\n%s" (pp a) msg

opTyErr :: String -> [Type] -> String -> Typing a
opTyErr op tys msg = throwError $ printf "CL type error: %s {%s}\n%s" op tyMsg msg
  where
    tyMsg = concat $ intersperse "," $ fmap pp tys

bindTy :: Ident -> Type -> TyEnv -> TyEnv
bindTy x ty tyEnv = (x,ty) : tyEnv

lookupTy :: Ident -> Typing Type
lookupTy x = do
    tyEnv <- ask
    case lookup x tyEnv of
        Just ty -> pure ty
        Nothing -> throwError $ printf "CL type error: %s not in type env %s" x (pp tyEnv)

type Typing = ReaderT TyEnv (Either String)

--------------------------------------------------------------------------------
-- Monadic type predicates

elemTy :: Type -> Typing Type
elemTy (ListT ty) = pure ty
elemTy ty         = throwError $ printf "CL type error: %s not a list type" (pp ty)

listTy :: Type -> Typing ()
listTy (ListT _) = pure ()
listTy ty        = throwError $ printf "CL type error: %s not a list type" (pp ty)

numTy :: Type -> Typing ()
numTy (ScalarT IntT)     = pure ()
numTy (ScalarT DoubleT)  = pure ()
numTy (ScalarT DecimalT) = pure ()
numTy ty                 = throwError $ printf "CL type error: %s not a numeric type" (pp ty)

boolTy :: Type -> Typing ()
boolTy (ScalarT BoolT) = pure ()
boolTy ty              = throwError $ printf "CL type error: %s not boolean" (pp ty)

fractTy :: Type -> Typing ()
fractTy (ScalarT DoubleT)  = pure ()
fractTy (ScalarT DecimalT) = pure ()
fractTy ty                 = throwError $ printf "CL type error: %s not a fractional type" (pp ty)

scalarTy :: Type -> Typing ScalarType
scalarTy (ScalarT sty) = pure sty
scalarTy ty            = throwError $ printf "CL type error: %s not a scalar type" (pp ty)

--------------------------------------------------------------------------------
-- Type inference

-- | Typing of unary builtins
tyPrim1 :: Prim1 -> Type -> Typing Type
tyPrim1 Singleton ty   = pure $ ListT ty
tyPrim1 Only ty        = catchError (elemTy ty) (opTyErr "only" [ty])
tyPrim1 Concat ty      =
    case ty of
        ListT (ListT eTy) -> pure $ ListT eTy
        _                 -> opTyErr "concat" [ty] ""
tyPrim1 Null ty        = do
    case ty of
        ListT _ -> pure $ ScalarT BoolT
        _       -> opTyErr "null" [ty] ""
tyPrim1 Reverse ty     = catchError (listTy ty) (opTyErr "reverse" [ty]) >> pure ty
tyPrim1 Nub ty         = catchError (listTy ty) (opTyErr "nub" [ty]) >> pure ty
tyPrim1 Number ty      = flip catchError (opTyErr "number" [ty]) $ do
    eTy <- elemTy ty
    pure $ ListT $ TupleT [eTy, ScalarT IntT]
tyPrim1 Sort ty        = do
    case ty of
        ListT (TupleT [ty1, _]) -> pure $ ListT ty1
        _                       -> opTyErr "sort" [ty] ""
tyPrim1 Group ty       = do
    case ty of
        ListT (TupleT [ty1, ty2]) -> pure $ ListT (TupleT [ty2, ListT ty1])
        _                         -> opTyErr "group" [ty] ""
tyPrim1 (GroupAgg as) ty =
    case ty of
        ListT (TupleT [ty1, ty2]) -> do
            aTys <- runReaderT (mapM aggrTy $ N.toList $ getNE as) (Just ty1)
            pure $ ListT (TupleT $ [ty2, ListT ty1] ++ aTys)
        _                         -> opTyErr "groupagg" [ty] ""
tyPrim1 Guard ty       = do
    case ty of
        ScalarT BoolT -> pure $ ListT $ ScalarT UnitT
        _             -> opTyErr "guard" [ty] ""
tyPrim1 (TupElem i) ty =
    case ty of
        TupleT tys -> maybe (opTyErr (printf "_.%d" (tupleIndex i)) [ty] "")
                            pure
                            (safeIndex i tys)
        _          -> opTyErr (printf "_.%d" (tupleIndex i)) [ty] ""
tyPrim1 (Agg a) ty     = flip catchError (opTyErr (pp a) [ty]) $ do
    eTy <- elemTy ty
    aggTy eTy a

aggTy :: Type -> AggrFun -> Typing Type
aggTy ty a =
    case a of
        Length _ -> pure $ ScalarT IntT
        Sum      -> numTy ty >> pure ty
        Avg      -> fractTy ty >> pure ty
        And      -> boolTy ty >> pure ty
        Or       -> boolTy ty >> pure ty
        Maximum  -> void (scalarTy ty) >> pure ty
        Minimum  -> void (scalarTy ty) >> pure ty

-- | Typing of binary builtins
tyPrim2 :: Prim2 -> Type -> Type -> Typing Type
tyPrim2 Append ty1 ty2           =
    if isList ty1 && isList ty2 && ty1 == ty2
    then pure ty1
    else opTyErr "append" [ty1, ty2] ""
tyPrim2 Zip ty1 ty2              = flip catchError (opTyErr "zip" [ty1,ty2]) $ do
    ety1 <- elemTy ty1
    ety2 <- elemTy ty2
    pure $ ListT $ TupleT [ety1, ety2]
tyPrim2 CartProduct ty1 ty2      = flip catchError (opTyErr "cartproduct" [ty1,ty2]) $ do
    ety1 <- elemTy ty1
    ety2 <- elemTy ty2
    pure $ ListT $ TupleT [ety1, ety2]
tyPrim2 (ThetaJoin p) ty1 ty2    = flip catchError (opTyErr "thetajoin" [ty1,ty2]) $ do
    ety1 <- elemTy ty1
    ety2 <- elemTy ty2
    checkPredTy ety1 ety2 p
    pure $ ListT $ TupleT [ety1, ety2]
tyPrim2 (NestJoin p) ty1 ty2     = flip catchError (opTyErr "nestjoin" [ty1, ty2]) $ do
    ety1 <- elemTy ty1
    ety2 <- elemTy ty2
    checkPredTy ety1 ety2 p
    pure $ ListT $ TupleT [ety1, ListT (TupleT [ety1, ety2])]
tyPrim2 (SemiJoin p) ty1 ty2     = flip catchError (opTyErr "semijoin" [ty1, ty2]) $ do
    ety1 <- elemTy ty1
    ety2 <- elemTy ty2
    checkPredTy ety1 ety2 p
    pure $ ListT ety1
tyPrim2 (AntiJoin p) ty1 ty2     = flip catchError (opTyErr "antijoin" [ty1, ty2]) $ do
    ety1 <- elemTy ty1
    ety2 <- elemTy ty2
    checkPredTy ety1 ety2 p
    pure $ ListT ety1
tyPrim2 (GroupJoin p as) ty1 ty2 = flip catchError (opTyErr "groupjoin" [ty1, ty2]) $ do
    ety1 <- elemTy ty1
    ety2 <- elemTy ty2
    checkPredTy ety1 ety2 p
    let tupTy = TupleT [ety1, ety2]
    aTys <- runReaderT (mapM aggrTy $ N.toList $ getNE as) (Just tupTy)
    case aTys of
        [aTy] -> pure $ ListT $ TupleT [ety1, aTy]
        _     -> pure $ ListT $ TupleT $ ety1 : aTys

tyComp :: NL Qual -> Expr -> Typing Type
tyComp (GuardQ p :* qs) h = do
    guardTy <- inferTy p
    case guardTy of
        ScalarT BoolT -> tyComp qs h
        _             -> throwError $ printf "guard: %s" (pp guardTy)
tyComp (S (GuardQ p)) h = do
    guardTy <- inferTy p
    case guardTy of
        ScalarT BoolT -> ListT <$> inferTy h
        _             -> throwError $ printf "guard: %s" (pp guardTy)
tyComp (BindQ x xs :* qs) h = do
    genTy <- inferTy xs >>= elemTy
    local (bindTy x genTy) $ tyComp qs h
tyComp (S (BindQ x xs)) h = do
    genTy <- inferTy xs >>= elemTy
    ListT <$> local (bindTy x genTy) (inferTy h)

-- | Typing of CL expressions
inferTy :: Expr -> Typing Type
inferTy (Table _ _ schema) =
    pure $ ListT $ TupleT $ N.toList $ fmap (ScalarT . snd) $ tableCols schema
inferTy a@(AppE1 _ p e)      = catchError (inferTy e >>= tyPrim1 p) (expTyErr a)
inferTy a@(AppE2 _ p e1 e2)  = do
    ty1 <- inferTy e1
    ty2 <- inferTy e2
    catchError (tyPrim2 p ty1 ty2) (expTyErr a)
inferTy (BinOp _ o e1 e2)    = do
    ty1 <- inferTy e1
    ty2 <- inferTy e2
    case (ty1, ty2) of
        (ScalarT sTy1, ScalarT sTy2) -> ScalarT <$> inferBinOpScalar sTy1 sTy2 o
        _                            -> opTyErr (pp o) [ty1, ty2] ""
inferTy (UnOp _ o e)         = do
    ty <- inferTy e
    case ty of
        ScalarT sTy -> ScalarT <$> inferUnOpScalar sTy o
        _           -> opTyErr (pp o) [ty] ""
inferTy (If _ c t e)         = do
    tyC <- inferTy c
    tyT <- inferTy t
    tyE <- inferTy e
    if tyC /= ScalarT BoolT || tyT /= tyE
       then opTyErr "if" [tyC, tyT, tyE] ""
       else pure tyT
inferTy (Lit ty _)           = pure ty
inferTy (Var _ x)            = lookupTy x
inferTy (Comp _ h qs)        = tyComp qs h
inferTy (MkTuple _ es)       = do
    tys <- mapM inferTy es
    pure $ TupleT tys
inferTy (Let _ x e1 e2)    = do
    ty1 <- inferTy e1
    local (bindTy x ty1) $ inferTy e2

-- | Infer the type of a CL expression
inferCLTy :: Expr -> Either String Type
inferCLTy e = runReaderT (inferTy e) []
