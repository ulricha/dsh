{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE LambdaCase          #-}
    
-- | Normalize patterns from source programs (not to be confused with
-- comprehension normalization)
module Database.DSH.CL.Opt.Normalize
  ( normalizeOnceR 
  , normalizeExprR
  ) where

import           Control.Arrow
import qualified Data.Foldable              as F
import qualified Data.Traversable           as T
       
import           Database.DSH.Impossible
import           Database.DSH.Common.Lang
import           Database.DSH.CL.Lang
import           Database.DSH.CL.Kure
import qualified Database.DSH.CL.Primitives as P
import           Database.DSH.CL.Opt.Aux

------------------------------------------------------------------
-- Simple normalization rewrites that are applied only at the start of
-- rewriting.

-- Rewrites that are expected to only match once in the beginning and whose
-- pattern should not occur due to subsequent rewrites.

-- | Split conjunctive predicates.
splitConjunctsR :: RewriteC (NL Qual)
splitConjunctsR = splitR <+ splitEndR
  where
    splitR :: RewriteC (NL Qual)
    splitR = do
        (GuardQ (BinOp _ (SBBoolOp Conj) p1 p2)) :* qs <- idR
        return $ GuardQ p1 :* GuardQ p2 :* qs
    
    splitEndR :: RewriteC (NL Qual)
    splitEndR = do
        (S (GuardQ (BinOp _ (SBBoolOp Conj) p1 p2))) <- idR
        return $ GuardQ p1 :* (S $ GuardQ p2)
        
normalizeOnceR :: RewriteC CL
normalizeOnceR = repeatR $ anytdR $ promoteR splitConjunctsR
    
------------------------------------------------------------------
-- Simple normalization rewrites that are interleaved with other rewrites.

pattern PEq e1 e2 <- BinOp _ (SBRelOp Eq) e1 e2
pattern PLength e <- AppE1 _ (Prim1 Length _) e
pattern PAnd xs <- AppE1 _ (Prim1 And _) xs
pattern POr xs <- AppE1 _ (Prim1 Or _) xs
pattern PNot e <- UnOp _ (SUBoolOp Not) e
pattern PNull e <- AppE1 _ (Prim1 Null _) e
pattern PTrue = Lit BoolT (BoolV True)

-- Bring a NOT EXISTS pattern into universal quantification form:
-- not (or [ q | y <- ys, ps ])
-- =>
-- and [ not q | y <- ys, ps ]
notExistsR :: RewriteC CL
notExistsR = promoteT $ readerT $ \e -> case e of
    -- With range predicates
    PNot (POr (Comp t q (BindQ y ys :* ps))) -> do
    
        -- All remaining qualifiers have to be guards.
        guardExprs           <- constT $ T.mapM fromGuard ps

        return $ inject $ P.and $ Comp t (P.not q) (BindQ y ys :* ps)

    -- Without range predicates
    PNot (POr (Comp t q (S (BindQ y ys)))) -> do
        return $ inject $ P.and $ Comp t (P.not q) (S $ BindQ y ys)

    _ -> fail "no match"

-- Normalization of null occurences
-- length xs == 0 => null xs
-- 0 == length xs => null xs
zeroLengthR :: RewriteC CL
zeroLengthR = promoteT $ readerT $ \e -> case e of
    PEq (PLength xs) (Lit _ (IntV 0)) -> return $ inject $ P.null xs
    PEq (Lit _ (IntV 0)) (PLength xs) -> return $ inject $ P.null xs
    _                                 -> fail "no match"

-- null [ _ | x <- xs, p1, p2, ... ] 
-- => and [ not (p1 && p2 && ...) | x <- xs ]
comprehensionNullR :: RewriteC CL
comprehensionNullR = do
    PNull (Comp _ _ qs) <- promoteT idR
    
    -- We need exactly one generator and at least one guard.
    BindQ x xs :* guards <- return $ qs
    guardExprs           <- constT $ T.mapM fromGuard guards

    -- Merge all guards into a conjunctive form
    let conjPred = P.not $ F.foldl1 P.conj guardExprs
    return $ inject $ P.and $ Comp (listT boolT) conjPred (S $ BindQ x xs)

normalizeExprR :: RewriteC CL
normalizeExprR = zeroLengthR 
                 <+ comprehensionNullR
                 <+ notExistsR
