{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}

-- | Monad comprehension normalization rules (adapted from T. Grust
-- "Comprehending Queries")
module Database.DSH.CL.Opt.CompNormalization
    ( m_norm_1R
    , m_norm_2R
    , m_norm_3R
    , m_norm_4R
    , m_norm_5R
    , invariantguardR
    , guardpushfrontR
    , ifgeneratorR
    , identityCompR
    , ifheadR
    ) where

import           Control.Applicative
import           Control.Arrow
import           Data.Either
import qualified Data.Map                   as M
import qualified Data.Set                   as S

import           Database.DSH.CL.Kure
import           Database.DSH.CL.Lang
import           Database.DSH.CL.Opt.Aux
import qualified Database.DSH.CL.Primitives as P
import           Database.DSH.Common.Kure
import           Database.DSH.Common.Lang
import           Database.DSH.Impossible

------------------------------------------------------------------
-- Classical Monad Comprehension Normalization rules (Grust)

-- | M-Norm-1: Eliminate comprehensions with empty generators
m_norm_1R :: RewriteC CL
m_norm_1R = do
    Comp t _ _ <- promoteT idR
    matches <- childT CompQuals $ onetdT (promoteT $ patternT <+ patternEndT)
    guardM matches
    return $ inject $ Lit t (ListV [])

  where
    patternT :: TransformC (NL Qual) Bool
    patternT = do
        BindQ _ (Lit _ (ListV [])) :* _ <- idR
        return True

    patternEndT :: TransformC (NL Qual) Bool
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
        constT (return $ inject $ P.sng h) >>> substR x e

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
    qualT :: TransformC Qual (Ident, Expr)
    qualT = do
        q <- idR
        case q of
            -- x <- [v]
            BindQ x (Lit t (ListV [v]))   -> return (x, Lit (elemT t) v)
            -- x <- v : []
            BindQ x (AppE1 _ Singleton v) -> return (x, v)
            _                             -> fail "qualR: no match"

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
    Comp t _ _ <- promoteT idR
    (tuplifyHeadR, qs') <- statefulT idR $ childT CompQuals (promoteR normQualifiersR) >>> projectT
    h'                  <- childT CompHead (tryR tuplifyHeadR) >>> projectT
    return $ inject $ Comp t h' qs'

  where

    qualT :: TransformC Qual (Ident, Expr, NL Qual)
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


--------------------------------------------------------------------------------
-- Additional normalization rules for comprehensions

qualsguardpushfrontR :: RewriteC (NL Qual)
qualsguardpushfrontR = do
    qs     <- idR
    -- Separate generators from guards
    ((g : gs), guards@(_:_)) <- return $ partitionEithers $ map fromQual $ toList qs

    let gens = fmap (uncurry BindQ) $ fromListSafe g gs
    env <- S.fromList <$> M.keys <$> cl_bindings <$> contextT
    let qs' = foldl (\quals guard -> insertGuard guard env quals) gens guards
    guardM $ qs /= qs'
    return qs'

-- | Push all guards as far as possible to the front of the qualifier
-- list.
guardpushfrontR :: RewriteC CL
guardpushfrontR = do
    Comp t h _ <- promoteT idR
    qs' <- childT CompQuals (promoteR qualsguardpushfrontR) >>> projectT
    return $ inject $ Comp t h qs'

-- | If a guard does not depend on any generators of the current
-- comprehension, it can be applied outside of the comprehension.
invariantguardR :: RewriteC CL
invariantguardR = do
    Comp t h (GuardQ g :* qs) <- promoteT idR
    return $ inject $ P.if_ g (Comp t h qs) (Lit t (ListV []))

ifgeneratorqualsR :: RewriteC (NL Qual)
ifgeneratorqualsR = anytdR $ readerT $ \quals -> case quals of
    BindQ x (If _ ce te (Lit _ (ListV []))) :* qs -> return $ BindQ x te :* GuardQ ce :* qs
    S (BindQ x (If _ ce te (Lit _ (ListV []))))   -> return $ BindQ x te :* S (GuardQ ce)
    _                                         -> fail "no match"


-- | Transform an 'if' conditional in a generator into a guard.
ifgeneratorR :: RewriteC CL
ifgeneratorR = do
    Comp t h _ <- promoteT idR
    qs' <- childT CompQuals (promoteR ifgeneratorqualsR) >>> projectT
    return $ inject $ Comp t h qs'

-- | Eliminate comprehensions that do not perform work.
identityCompR :: RewriteC CL
identityCompR = do
    Comp _ (Var _ x) (S (BindQ x' xs)) <- promoteT idR
    guardM $ x == x'
    return $ inject xs

-- | Merge an 'if' expression in a comprehension head into the
-- comprehension.
ifheadR :: RewriteC CL
ifheadR = do
    Comp t (If _ ce te (Lit _ (ListV []))) qs <- promoteT idR
    return $ inject $ Comp t te (appendNL qs (S $ GuardQ ce))
