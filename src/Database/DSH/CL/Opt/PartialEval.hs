{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE TemplateHaskell     #-}
    
-- | Support rewrites (partial evaluation, house cleaning)
module Database.DSH.CL.Opt.PartialEval
  ( partialEvalR
  ) where
  
import           Database.DSH.Common.Nat
import           Database.DSH.CL.Lang
import           Database.DSH.CL.Kure

--------------------------------------------------------------------------------
-- Partial evaluation rules

-- | Eliminate tuple construction if the elements are first and second of the
-- same pair:
-- pair (fst x) (snd x) => x
identityPairR :: RewriteC CL
identityPairR = do
    ExprCL (MkTuple _ [ AppE1 _ (TupElem First)  v@(Var tupleTy x) 
                      , AppE1 _ (TupElem (Next First)) (Var _ x')
                      ]) <- idR

    -- Check that the original value actually was a /pair/ and that no
    -- elements are discarded.
    TupleT [_, _] <- return tupleTy

    guardM $ x == x'
    return $ inject v

tupleElemR :: RewriteC CL
tupleElemR = do
    ExprCL (AppE1 _ (TupElem i) (MkTuple _ es)) <- idR
    return $ inject $ es !! (tupleIndex i - 1)

partialEvalR :: RewriteC CL
partialEvalR = 
    readerT $ \cl -> case cl of
        ExprCL AppE1{}   -> tupleElemR
        ExprCL MkTuple{} -> identityPairR
        _                -> fail "can't apply partial evaluation rules"
