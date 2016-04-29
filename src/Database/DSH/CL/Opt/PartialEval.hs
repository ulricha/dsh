{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Support rewrites (partial evaluation, house cleaning)
module Database.DSH.CL.Opt.PartialEval
  ( partialEvalR
  ) where

import           Database.DSH.CL.Kure
import           Database.DSH.CL.Lang
import           Database.DSH.CL.Opt.Auxiliary
import           Database.DSH.Common.Lang
import           Database.DSH.Common.Nat

--------------------------------------------------------------------------------
-- Partial evaluation rules

-- | Eliminate tuple construction if the elements are first and second of the
-- same pair:
-- pair (fst x) (snd x) => x
identityPairR :: RewriteC CL
identityPairR = do
    MkTuple _ [ AppE1 _ (TupElem First)  v@(Var tupleTy x)
              , AppE1 _ (TupElem (Next First)) (Var _ x')
              ] <- promoteT idR

    -- Check that the original value actually was a /pair/ and that no
    -- elements are discarded.
    TupleT [_, _] <- return tupleTy

    guardM $ x == x'
    return $ inject v

tupleElemR :: RewriteC CL
tupleElemR = do
    AppE1 _ (TupElem i) (MkTuple _ es) <- promoteT idR
    return $ inject $ es !! (tupleIndex i - 1)

negationR :: RewriteC CL
negationR =
    readerT $ \cl -> case cl of
        ExprCL (NotP (NotP e)) -> return $ inject e
        ExprCL (NotP TrueP)    -> return $ inject FalseP
        ExprCL (NotP FalseP)   -> return $ inject TrueP
        _                      -> fail "no negation to optimize"

fromLiteral :: Expr -> TransformC CL Val
fromLiteral (Lit _ val) = return val
fromLiteral _           = fail "not a literal"

literalTupleR :: RewriteC CL
literalTupleR = do
    MkTuple tupTy elems <- promoteT idR
    vals                <- mapM fromLiteral elems
    return $ inject $ Lit tupTy $ TupleV vals

literalAppendR :: RewriteC CL
literalAppendR = do
    AppE2 listTy Append x y <- promoteT idR
    ListV xVals             <- fromLiteral x
    ListV yVals             <- fromLiteral y
    return $ inject $ Lit listTy $ ListV $ xVals ++ yVals

literalSingletonR :: RewriteC CL
literalSingletonR = do
    AppE1 listTy Singleton x <- promoteT idR
    xVal                     <- fromLiteral x
    return $ inject $ Lit listTy $ ListV [xVal]

appendEmptyLeftR :: RewriteC CL
appendEmptyLeftR = do
    AppE2 _ Append (Lit _ (ListV [])) ys <- promoteT idR
    return $ inject ys

appendEmptyRightR :: RewriteC CL
appendEmptyRightR = do
    AppE2 _ Append xs (Lit _ (ListV [])) <- promoteT idR
    return $ inject xs

partialEvalR :: RewriteC CL
partialEvalR =
    readerT $ \cl -> case cl of
        ExprCL UnOp{}    -> negationR
        ExprCL AppE1{}   -> tupleElemR <+ literalSingletonR
        ExprCL MkTuple{} -> identityPairR <+ literalTupleR
        ExprCL AppE2{}   -> literalAppendR <+ appendEmptyLeftR <+ appendEmptyRightR
        _                -> fail "can't apply partial evaluation rules"
