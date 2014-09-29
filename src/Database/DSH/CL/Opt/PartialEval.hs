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
-- same tuple:
-- pair (fst x) (snd x) => x
{-
FIXME add equivalent rewrite for proper tuples
pairR :: RewriteC CL
pairR = do
    ExprCL (AppE2 _ Pair
                    (AppE1 _ Fst v@(Var _ x)) 
                    (AppE1 _ Snd (Var _ x'))) <- idR
    guardM $ x == x'
    return $ inject v
-}

tupleElemR :: RewriteC CL
tupleElemR = do
    ExprCL (AppE1 _ (TupElem i) (MkTuple _ es)) <- idR
    return $ inject $ es !! (tupleIndex i - 1)

partialEvalR :: RewriteC CL
partialEvalR = 
    readerT $ \cl -> case cl of
        ExprCL AppE1{} -> tupleElemR
        -- ExprCL AppE2{} -> pairR
        _                    -> fail "can't apply partial evaluation rules"
