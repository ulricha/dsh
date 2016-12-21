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
    , guardpushbackR
    , ifgeneratorR
    , identityCompR
    ) where

import           Control.Arrow
import           Data.Either
import qualified Data.Map                   as M
import qualified Data.Set                   as S

import           Database.DSH.CL.Kure
import           Database.DSH.CL.Lang
import           Database.DSH.CL.Opt.Auxiliary
import qualified Database.DSH.CL.Primitives as P
import           Database.DSH.Common.Kure
import           Database.DSH.Common.Lang
import           Database.DSH.Common.Impossible

------------------------------------------------------------------
-- Classical Monad Comprehension Normalization rules (Grust)

-- | M-Norm-1: Eliminate comprehensions with empty generators
m_norm_1R :: RewriteC CL
m_norm_1R = logR "compnorm.M-Norm-1" $ do
    Comp t _ _ <- promoteT idR
    matches <- childT CompQuals $ onetdT (promoteT $ patternT <+ patternEndT)
    guardM matches
    return $ inject $ P.nil t

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
m_norm_2R = logR "compnorm.M-Norm-2" $ normSingletonCompR <+ normCompR

  where
    -- This rewrite is a bit annoying: If it triggers, we can remove a
    -- qualifier. However, the type NL forces us to take care that we do not
    -- produce a comprehension with an empty qualifier list.

    -- Due to non-empty NL lists, we have to consider the case of
    -- removing a (the!) qualifier from a singleton list.
    normSingletonCompR :: RewriteC CL
    normSingletonCompR = do
        Comp _ h (S q) <- promoteT idR
        (x, e)         <- constT $ matchingQualM q
        scopeNames     <- contextonlyT (pure . M.keysSet . clBindings)
        pure $ inject $ substE scopeNames x e (P.sng h)

    -- The main rewrite
    normCompR :: RewriteC CL
    normCompR = do
        Comp ty h _ <- promoteT idR
        (h', qs')   <- statefulT h $ childT CompQuals normQualifiersR >>> projectT
        pure $ inject $ Comp ty h' qs'

    normQualifiersR :: Rewrite CompCtx (RewriteStateM Expr RewriteLog) CL
    normQualifiersR = anytdR (normQualsEndR <+ normQualsR)

    -- -- Match the pattern (singleton generator) on a qualifier
    matchingQualM :: MonadCatch m => Qual -> m (Ident, Expr)
    matchingQualM q =
        case q of
            -- x <- [v]
            BindQ x (Lit t (ListV [v]))   -> pure (x, Lit (elemT t) v)
            -- x <- v : []
            BindQ x (AppE1 _ Singleton v) -> pure (x, v)
            _                             -> fail "qualR: no match"

    -- Try to match the pattern at the end of the qualifier list
    normQualsEndR :: Rewrite CompCtx (RewriteStateM Expr RewriteLog) CL
    normQualsEndR = do
        q1 :* S q2 <- promoteT idR
        (x, e)     <- constT $ matchingQualM q2
        scopeNames <- contextonlyT (pure . M.keysSet . clBindings)
        constT $ modify $ substE scopeNames x e
        pure $ inject $ S q1

    -- Try to match the pattern in the middle of the qualifier list
    normQualsR :: Rewrite CompCtx (RewriteStateM Expr RewriteLog) CL
    normQualsR = do
        q1 :* q2 :* qs <- promoteT idR
        (x, e)         <- constT $ matchingQualM q2
        h              <- constT get
        scopeNames     <- contextonlyT (pure . M.keysSet . clBindings)
        let (qs', h') = substCompE scopeNames x e qs h
        constT $ put h'
        pure $ inject $ q1 :* qs'

-- | M-Norm-3: unnest comprehensions from a generator
-- [ h | qs, x <- [ h' | qs'' ], qs' ]
-- => [ h[h'/x] | qs, qs'', qs'[h'/x] ]
m_norm_3R :: RewriteC CL
m_norm_3R = logR "compnorm.M-Norm-3" $ do
    Comp t h _ <- promoteT idR
    (h', qs')  <- statefulT h $ childT CompQuals (promoteR normQualifiersR) >>> projectT
    return $ inject $ Comp t h' qs'

  where

    matchingQualM :: MonadCatch m => Qual -> m (Ident, Expr, NL Qual)
    matchingQualM (BindQ x (Comp _ h qs)) = pure (x, h, qs)
    matchingQualM _                       = fail "m_norm_3R: no match"

    normQualifiersR :: Rewrite CompCtx (RewriteStateM Expr RewriteLog) (NL Qual)
    normQualifiersR = anytdR (normQualsEndR <+ normQualsR)

    normQualsEndR :: Rewrite CompCtx (RewriteStateM Expr RewriteLog) (NL Qual)
    normQualsEndR = do
        (S q) <- idR
        (x, h, qs) <- constT $ matchingQualM q
        scopeNames <- contextonlyT (pure . M.keysSet . clBindings)
        constT $ modify $ substE scopeNames x h
        pure qs

    normQualsR :: Rewrite CompCtx (RewriteStateM Expr RewriteLog) (NL Qual)
    normQualsR = do
        q :* qs      <- idR
        (x, hi, qsi) <- constT $ matchingQualM q
        h <- constT get
        scopeNames   <- contextonlyT (pure . M.keysSet . clBindings)
        let (qs', h') = substCompE scopeNames x hi qs h
        constT $ put h'
        pure $ appendNL qsi qs'

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
    (g : gs, guards@(_:_)) <- return $ partitionEithers $ map fromQual $ toList qs

    let gens = uncurry BindQ <$> fromListSafe g gs
    env <- S.fromList . M.keys . clBindings <$> contextT
    let qs' = foldl (\quals guard -> insertGuard guard env quals) gens guards
    guardM $ qs /= qs'
    return qs'

-- | Push all guards as far as possible to the front of the qualifier
-- list. Note that 'guardpushfrontR' loops with join introduction
-- rewrites and must not be isolated.
guardpushfrontR :: RewriteC CL
guardpushfrontR = do
    Comp t h _ <- promoteT idR
    qs' <- childT CompQuals (promoteR qualsguardpushfrontR) >>> projectT
    return $ inject $ Comp t h qs'

-- FIXME this is not correct if name shadowing occurs in the generators:
-- [ e | x <- xs, p x, x <- ys ]
pushBackGuards :: NL Qual -> NL Qual
pushBackGuards qs =
    case (map (uncurry BindQ) gens, map GuardQ preds) of
        (g:gs, ps) -> fromListSafe g (gs ++ ps)
        ([], _)    -> $impossible
  where
    (gens, preds) = partitionEithers $ map fromQual $ toList qs

-- | Push all guards to the end of the qualifier list to bring
-- generators closer together.
guardpushbackR :: RewriteC CL
guardpushbackR = logR "compnorm.guardpushback" $ do
    Comp t h qs <- promoteT idR
    let qs' = pushBackGuards qs
    guardM $ qs /= qs'
    return $ inject $ Comp t h qs'

-- | If a guard does not depend on any generators of the current
-- comprehension, it can be evaluated outside of the comprehension. As
-- preparation, we push guards towards the front of the qualifier
-- list.
invariantguardR :: RewriteC CL
invariantguardR = logR "compnorm.invariantguard" $
    tryR guardpushfrontR
    >>>
    promoteR (readerT $ \expr -> case expr of
        Comp t h (GuardQ g :* qs) -> return $ inject $ P.if_ g (Comp t h qs) (P.nil t)
        Comp t h (S (GuardQ p))   -> return $ inject $ P.if_ p (P.sng h) (P.nil t)
        _                         -> fail "no match")

ifgeneratorqualsR :: RewriteC (NL Qual)
ifgeneratorqualsR = anytdR $ readerT $ \quals -> case quals of
    BindQ x (If _ ce te (Lit _ (ListV []))) :* qs -> return $ BindQ x te :* GuardQ ce :* qs
    S (BindQ x (If _ ce te (Lit _ (ListV []))))   -> return $ BindQ x te :* S (GuardQ ce)
    _                                         -> fail "no match"


-- | Transform an 'if' conditional in a generator into a guard.
ifgeneratorR :: RewriteC CL
ifgeneratorR = logR "compnorm.ifgenerator" $ do
    Comp t h _ <- promoteT idR
    qs' <- childT CompQuals (promoteR ifgeneratorqualsR) >>> projectT
    return $ inject $ Comp t h qs'

-- | Eliminate comprehensions that do not perform work.
identityCompR :: RewriteC CL
identityCompR = logR " compnorm.identitycomp" $ do
    Comp _ (Var _ x) (S (BindQ x' xs)) <- promoteT idR
    guardM $ x == x'
    return $ inject xs
