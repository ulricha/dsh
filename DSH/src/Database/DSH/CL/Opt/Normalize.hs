{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE TemplateHaskell     #-}
    
-- | Normalize patterns from source programs (not to be confused with
-- comprehension normalization)
module Database.DSH.CL.Opt.Normalize
  ( normalizeR ) where
  
import Debug.Trace
       
import           Database.DSH.CL.Lang
import           Database.DSH.CL.Kure
import qualified Database.DSH.CL.Primitives as P
import           Database.DSH.CL.Opt.Support
import           Database.DSH.CL.Opt.Aux

------------------------------------------------------------------
-- Simple normalization rewrites

-- These rewrites are meant to only normalize certain patterns stemming from the
-- source program. They are expected to only match once at the beginning of
-- optimization.

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
    c <- idR
    debugUnit "normalizeUniversalR" c
    GuardQ (BinOp _ Eq 
                (AppE1 _ (Prim1 Length _) 
                    (Comp _ _ (BindQ x xs :* (S (GuardQ p)))))
                (Lit _ (IntV 0))) <- idR

    return $ GuardQ (P.and (Comp (listT boolT) 
                           (P.not p) 
                           (S (BindQ x xs))))
                           
    
normalizeR :: RewriteC CL
normalizeR = repeatR $ anytdR $ promoteR splitConjunctsR
                                <+ promoteR normalizeExistentialR
                                <+ promoteR normalizeUniversalR
