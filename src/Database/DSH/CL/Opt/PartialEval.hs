{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE TemplateHaskell     #-}
    
-- | Support rewrites (partial evaluation, house cleaning)
module Database.DSH.CL.Opt.PartialEval
  ( partialEvalR
  ) where
  
import           Database.DSH.Common.Nat
import           Database.DSH.Common.Lang
import           Database.DSH.CL.Lang
import           Database.DSH.CL.Kure

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
    AppE2 listTy Append x xs <- promoteT idR
    xVal                     <- fromLiteral x
    ListV xsVals             <- fromLiteral xs
    return $ inject $ Lit listTy $ ListV $ xVal : xsVals

literalSingletonR :: RewriteC CL
literalSingletonR = do
    AppE1 listTy Singleton x <- promoteT idR
    xVal                     <- fromLiteral x
    return $ inject $ Lit listTy $ ListV [xVal]

partialEvalR :: RewriteC CL
partialEvalR = 
    readerT $ \cl -> case cl of
        ExprCL AppE1{}   -> tupleElemR <+ literalSingletonR
        ExprCL MkTuple{} -> identityPairR <+ literalTupleR
        ExprCL AppE2{}   -> literalAppendR
        _                -> fail "can't apply partial evaluation rules"
