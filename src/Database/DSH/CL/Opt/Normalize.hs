{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE LambdaCase          #-}
    
-- | Normalize patterns from source programs (not to be confused with
-- comprehension normalization)
module Database.DSH.CL.Opt.Normalize
  ( normalizeOnceR 
  , normalizeAlwaysR
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

------------------------------------------------------------------
-- Normalization of null occurences

-- length xs == 0 => null xs
zeroLengthLeftR :: RewriteC CL
zeroLengthLeftR = do
    (BinOp _ (SBRelOp Eq)
             (AppE1 _ (Prim1 Length _) xs)
             (Lit _ (IntV 0))) <- promoteT idR

    return $ inject $ P.null xs

-- 0 == length xs => null xs
zeroLengthRightR :: RewriteC CL
zeroLengthRightR = do
    (BinOp _ (SBRelOp Eq)
             (Lit _ (IntV 0))
             (AppE1 _ (Prim1 Length _) xs)) <- promoteT idR

    return $ inject $ P.null xs

-- null [ _ | x <- xs, p1, p2, ... ] 
-- => and [ not (p1 && p2 && ...) | x <- xs ]
comprehensionNullR :: RewriteC CL
comprehensionNullR = do
    AppE1 _ (Prim1 Null _) (Comp _ _ qs) <- promoteT idR
    
    -- We need exactly one generator and at least one guard.
    BindQ x xs :* guards <- return $ qs
    guardExprs           <- constT $ T.mapM fromGuard guards

    -- Merge all guards into a conjunctive form
    let conjPred = P.not $ F.foldl1 P.conj guardExprs
    return $ inject $ P.and $ Comp boolT conjPred (S $ BindQ x xs)

normalizeExprs :: RewriteC CL
normalizeExprs = zeroLengthLeftR <+ zeroLengthRightR

normalizeAlwaysR :: RewriteC CL
normalizeAlwaysR = normalizeExprs

