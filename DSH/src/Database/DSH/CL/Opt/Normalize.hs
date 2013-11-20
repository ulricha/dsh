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
import           Debug.Trace
       
import           Database.DSH.CL.Lang
import           Database.DSH.CL.Kure
import qualified Database.DSH.CL.Primitives as P
import           Database.DSH.CL.Opt.Support
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
        (GuardQ (BinOp _ Conj p1 p2)) :* qs <- idR
        return $ GuardQ p1 :* GuardQ p2 :* qs
    
    splitEndR :: RewriteC (NL Qual)
    splitEndR = do
        (S (GuardQ (BinOp _ Conj p1 p2))) <- idR
        return $ GuardQ p1 :* (S $ GuardQ p2)
        
normalizeOnceR :: RewriteC CL
normalizeOnceR = repeatR $ anytdR $ promoteR splitConjunctsR
    
------------------------------------------------------------------
-- Simple normalization rewrites that are interleaved with other rewrites.

-- These rewrites are meant to only normalize certain patterns stemming from the
-- source program. However, they have to be interleaved with general
-- comprehension unnesting and optimization, as they might depend on a pushdown
-- of predicates, e.g.:

-- [ ... | y <- ys, not $ null [ e | x <- xs, p x y, q x ] ]
-- => 
-- [ ... | y <- ys, not $ null [ e | x <- filter (\x -> q x) xs, p x y ]
-- =>
-- [ ... | y <- ys, or [ p x y | x <- filter (\x -> q x) ] ]

-- | Normalize a guard expressing existential quantification:
-- not $ null [ ... | x <- xs, p ] (not $ length [ ... ] == 0)
-- => or [ p | x <- xs ]
normalizeExistentialR :: RewriteC Qual
normalizeExistentialR = do
    GuardQ (AppE1 _ (Prim1 Not _) 
               (BinOp _ Eq 
                   (AppE1 _ (Prim1 Length _) 
                       (Comp _ _ (BindQ x xs :* (S (GuardQ p)))))
                   (Lit _ (IntV 0)))) <- idR

    return $ GuardQ (P.or (Comp (listT boolT) 
                          p 
                          (S (BindQ x xs))))

-- | Normalize a guard expressing universal quantification:
-- [ ... | x <- xs, p ] (length [ ... ] == 0)
-- => and [ p | x <- xs ]
normalizeUniversalR :: RewriteC Qual
normalizeUniversalR = do
    -- c <- idR
    -- debugUnit "normalizeUniversalR" c
    GuardQ (BinOp _ Eq 
                (AppE1 _ (Prim1 Length _) 
                    (Comp _ _ (BindQ x xs :* (S (GuardQ p)))))
                (Lit _ (IntV 0))) <- idR

    return $ GuardQ (P.and (Comp (listT boolT) 
                           (P.not p) 
                           (S (BindQ x xs))))
                           
normQualR :: RewriteC Qual
normQualR = normalizeExistentialR <+ normalizeUniversalR
    
normalizeQualifiersR :: RewriteC (NL Qual)
normalizeQualifiersR = 
    anytdR $ readerT $ \case
        q :* qs -> do
            q' <- constT (return q) >>> normQualR
            return $ q' :* qs
        S q     -> do
            q' <- constT (return q) >>> normQualR
            return $ S q'
                      
normalizeAlwaysR :: RewriteC CL
normalizeAlwaysR = do
    Comp _ _ _ <- promoteT idR 
    childR 1 $ promoteR normalizeQualifiersR
