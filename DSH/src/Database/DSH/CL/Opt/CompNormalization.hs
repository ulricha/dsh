{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE TemplateHaskell     #-}
    
-- | Monad comprehension normalization rules (adapted from T. Grust
-- "Comprehending Queries")
module Database.DSH.CL.Opt.CompNormalization
  ( m_norm_1R
  , m_norm_2R
  , m_norm_3R
  , m_norm_4R
  , m_norm_5R
  ) where
       
import Control.Arrow
                 
import Database.DSH.Impossible
import Database.DSH.Common.Lang
import Database.DSH.CL.Lang
import Database.DSH.CL.Kure
import Database.DSH.CL.Opt.Aux

------------------------------------------------------------------
-- Monad Comprehension Normalization rules
   
-- | M-Norm-1: Eliminate comprehensions with empty generators
m_norm_1R :: RewriteC CL
m_norm_1R = do
    Comp t _ _ <- promoteT idR
    matches <- childT CompQuals $ onetdT (promoteT $ patternT <+ patternEndT)
    guardM matches
    return $ inject $ Lit t (ListV [])
    
  where 
    patternT :: TranslateC (NL Qual) Bool
    patternT = do
        BindQ _ (Lit _ (ListV [])) :* _ <- idR
        return True
        
    patternEndT :: TranslateC (NL Qual) Bool
    patternEndT = do
        (S (BindQ _ (Lit _ (ListV [])))) <- idR
        return True

-- | M-Norm-2: eliminate singleton generators.
-- [ h | qs, x <- [v], qs' ]
-- => [ h[v/x] | qs, qs'[v/x] ]
m_norm_2R :: RewriteC CL
m_norm_2R = (normSingletonCompR <+ normCompR) >>> debugTrace "m_norm_2"
    
  where
    -- This rewrite is a bit annoying: If it triggers, we can remove a
    -- qualifier. However, the type NL forces us to take care that we do not
    -- produce a comprehension with an empty qualifier list.
    
    -- Due to non-empty NL lists, we have to consider the case of
    -- removing a (the!) qualifier from a singleton list.
    normSingletonCompR :: RewriteC CL
    normSingletonCompR = do
        Comp _ h (S q) <- promoteT idR
        (x, e) <- constT (return q) >>> qualT
        constT (return $ inject h) >>> substR x e
    
    -- The main rewrite
    normCompR :: RewriteC CL
    normCompR = do
        Comp t _ (_ :* _)   <- promoteT idR
        (tuplifyHeadR, qs') <- statefulT idR $ childT CompQuals (promoteR normQualifiersR) >>> projectT
        h'                  <- childT CompHead tuplifyHeadR >>> projectT
        return $ inject $ Comp t h' qs'
        
    normQualifiersR :: Rewrite CompCtx TuplifyM (NL Qual)
    normQualifiersR = anytdR (normQualsEndR <+ normQualsR)

    -- Match the pattern (singleton generator) on a qualifier
    qualT :: TranslateC Qual (Ident, Expr)
    qualT = do
        q <- idR
        case q of
            -- x <- [v]
            BindQ x (Lit t (ListV [v]))                 -> return (x, Lit (elemT t) v)
            -- x <- v : []
            BindQ x (AppE2 _ (Prim2 Cons _) v (Lit _ (ListV []))) -> return (x, v)
            _                                           -> fail "qualR: no match"
            
    -- Try to match the pattern at the end of the qualifier list
    normQualsEndR :: Rewrite CompCtx TuplifyM (NL Qual)
    normQualsEndR = do
        q1 :* (S q2) <- idR
        (x, e)       <- liftstateT $ constT (return q2) >>> qualT
        constT $ modify (>>> substR x e)
        return (S q1)
        
    -- Try to match the pattern in the middle of the qualifier list
    normQualsR :: Rewrite CompCtx TuplifyM (NL Qual)
    normQualsR = do
        q1 :* q2 :* qs <- idR
        (x, e)         <- liftstateT $ constT (return q2) >>> qualT
        qs' <- liftstateT $ constT (return $ inject qs) >>> substR x e >>> projectT
        constT $ modify (>>> substR x e)
        return $ q1 :* qs' 
        
-- | M-Norm-3: unnest comprehensions from a generator
-- [ h | qs, x <- [ h' | qs'' ], qs' ]
-- => [ h[h'/x] | qs, qs'', qs'[h'/x] ]
m_norm_3R :: RewriteC CL
m_norm_3R = do
    Comp t h _ <- promoteT idR
    (tuplifyHeadR, qs') <- statefulT idR $ childT CompQuals (promoteR normQualifiersR) >>> projectT
    h'                  <- childT CompHead (tryR tuplifyHeadR) >>> projectT
    return $ inject $ Comp t h' qs'
    
  where
  
    qualT :: TranslateC Qual (Ident, Expr, NL Qual)
    qualT = do
        BindQ x (Comp _ h' qs'') <- idR
        return (x, h', qs'')
        
    normQualifiersR :: Rewrite CompCtx TuplifyM (NL Qual)
    normQualifiersR = anytdR (normQualsEndR <+ normQualsR)
       
    normQualsEndR :: Rewrite CompCtx TuplifyM (NL Qual)
    normQualsEndR = do
        (S q) <- idR
        (x, h', qs'') <- liftstateT $ (constT $ return q) >>> qualT
        constT $ modify (>>> substR x h')
        return qs''
        
    normQualsR :: Rewrite CompCtx TuplifyM (NL Qual)
    normQualsR = do
        q :* qs <- idR
        (x, h', qs'') <- liftstateT $ (constT $ return q) >>> qualT
        qs' <- liftstateT $ constT (return $ inject qs) >>> substR x h' >>> projectT
        constT $ modify (>>> substR x h')
        return $ appendNL qs'' qs'
        
-- | M-Norm-4: unnest existential quantifiers if the outer comprehension is over
-- an idempotent monad (i.e. duplicates are eliminated from the result).
m_norm_4R :: RewriteC CL
m_norm_4R = $unimplemented

-- | M-Norm-5: Unnest nested comprehensions over an idempotent monad.
m_norm_5R :: RewriteC CL
m_norm_5R = $unimplemented

