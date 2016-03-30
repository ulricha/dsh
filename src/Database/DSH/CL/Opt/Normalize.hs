{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE TemplateHaskell     #-}

-- | Normalize patterns from source programs (not to be confused with
-- comprehension normalization)
module Database.DSH.CL.Opt.Normalize
  ( normalizeOnceR
  , normalizeExprR
  ) where

import           Control.Monad
import           Control.Arrow
import qualified Data.Foldable              as F
import qualified Data.Traversable           as T
import           Data.Monoid

import           Database.DSH.Common.Impossible
import           Database.DSH.Common.Lang
import           Database.DSH.CL.Lang
import           Database.DSH.CL.Kure
import qualified Database.DSH.CL.Primitives as P
import           Database.DSH.CL.Opt.Auxiliary

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
        GuardQ (BinOp _ (SBBoolOp Conj) p1 p2) :* qs <- idR
        return $ GuardQ p1 :* GuardQ p2 :* qs

    splitEndR :: RewriteC (NL Qual)
    splitEndR = do
        (S (GuardQ (BinOp _ (SBBoolOp Conj) p1 p2))) <- idR
        return $ GuardQ p1 :* (S $ GuardQ p2)

normalizeOnceR :: RewriteC CL
normalizeOnceR = repeatR $ anytdR $ promoteR splitConjunctsR

--------------------------------------------------------------------------------
-- Simple normalization rewrites that are interleaved with other rewrites.

normalizeExprR :: RewriteC CL
normalizeExprR = readerT $ \expr -> case expr of
    ExprCL AppE1{} -> comprehensionNullR
    ExprCL UnOp{}  -> notNullR <+ notExistsR
    ExprCL BinOp{} -> zeroLengthR
    ExprCL Let{}   -> unusedBindingR <+ simpleBindingR <+ referencedOnceR
    _              -> fail "not a normalizable expression"

--------------------------------------------------------------------------------
-- Normalization rewrites for universal/existential quantification.

-- Bring a NOT EXISTS pattern into universal quantification form:
-- not (or [ q | y <- ys, ps ])
-- =>
-- and [ not q | y <- ys, ps ]
notExistsR :: RewriteC CL
notExistsR = promoteT $ readerT $ \e -> case e of
    -- Don't rewrite if we don't have any predicate. Predicates may be hidden in
    -- nested comprehensions in the generator.
    NotP (OrP (Comp _ (Lit _ (ScalarV (BoolV True))) (S (_ :<-: _)))) ->
        fail "too early"

    NotP (OrP (Comp ty (Lit _ (ScalarV (BoolV True))) ((y :<-: ys) :* S (GuardQ p)))) ->
        return $ inject $ P.and $ Comp ty (P.not p) (S (y :<-: ys))

    NotP (OrP (Comp ty (Lit _ (ScalarV (BoolV True))) ((y :<-: ys) :* qs))) -> do
        ps <- constT $ T.mapM fromGuard qs
        let p = foldl1 P.conj ps
        return $ inject $ P.and $ Comp ty (P.not p) (S (y :<-: ys))

    -- With range predicates
    NotP (OrP (Comp t q (BindQ y ys :* ps))) -> do
        -- All remaining qualifiers have to be guards.
        void $ constT $ T.mapM fromGuard ps

        return $ inject $ P.and $ Comp t (P.not q) (BindQ y ys :* ps)

    -- Without range predicates
    NotP (OrP (Comp t q (S (BindQ y ys)))) ->
        return $ inject $ P.and $ Comp t (P.not q) (S $ BindQ y ys)

    _ -> fail "no match"

-- Normalization of null occurences
-- length xs == 0 => null xs
-- 0 == length xs => null xs
zeroLengthR :: RewriteC CL
zeroLengthR = promoteT $ readerT $ \e -> case e of
    EqP (LengthP xs) (Lit _ (ScalarV (IntV 0))) -> return $ inject $ P.null xs
    EqP (Lit _ (ScalarV (IntV 0))) (LengthP xs) -> return $ inject $ P.null xs
    _                                 -> fail "no match"

-- null [ _ | x <- xs, p1, p2, ... ]
-- => and [ not (p1 && p2 && ...) | x <- xs ]
comprehensionNullR :: RewriteC CL
comprehensionNullR = do
    NullP (Comp _ _ (BindQ x xs :* guards)) <- promoteT idR

    -- We need exactly one generator and at least one guard.
    guardExprs           <- constT $ T.mapM fromGuard guards

    -- Merge all guards into a conjunctive form
    let conjPred = P.not $ F.foldl1 P.conj guardExprs
    return $ inject $ P.and $ Comp (ListT PBoolT) conjPred (S $ BindQ x xs)

-- not $ null [ _ | x <- xs, ps ]
-- =>
-- not $ and [ not ps | x <- xs ] (comprehensionNullR)
-- =>
-- or [ ps | x <- xs ]
notNullR :: RewriteC CL
notNullR = do
    NotP (AndP (Comp _ (NotP p) (S (BindQ x xs)))) <- promoteT idR
    return $ inject $ P.or (Comp (ListT PBoolT) p (S (BindQ x xs)))

--------------------------------------------------------------------------------
-- Inline let bindings

-- | This function inlines let-bound expressions. In contrast to
-- general substitution, we do not inline into comprehensions, even if
-- we could. The reason is that expressions should not be evaluated
-- iteratively if they are loop-invariant.
inlineBindingR :: Ident -> Expr -> RewriteC CL
inlineBindingR v s = readerT $ \expr -> case expr of
    -- Occurence of the variable to be replaced
    ExprCL (Var _ n) | n == v          -> return $ inject s

    -- If a let-binding shadows the name we substitute, only descend
    -- into the bound expression.
    ExprCL (Let _ n _ _) | n == v      -> promoteR $ letR (extractR $ inlineBindingR v s) idR
                         | otherwise   ->
        if n `elem` freeVars s
        -- If the let-bound name occurs free in the substitute,
        -- alpha-convert the binding to avoid capturing the name.
        then $unimplemented >>> anyR (substR v s)
        else anyR $ inlineBindingR v s

    -- We don't inline into comprehensions to avoid conflicts with
    -- loop-invariant extraction.
    ExprCL Comp{}                      -> idR
    ExprCL _                           -> anyR $ inlineBindingR v s
    _                                  -> $impossible

-- | Count all occurences of an identifier for let-inlining.
countVarRefT :: Ident -> TransformC CL (Sum Int)
countVarRefT v = readerT $ \expr -> case expr of
    -- Occurence of the variable to be replaced
    ExprCL (Var _ n) | n == v          -> return 1
                     | otherwise       -> return 0

    ExprCL (Let _ n _ _) | n == v      -> promoteT $ letT (constT $ return 0)
                                                          (extractT $ countVarRefT v)
                                                          (\_ _ c1 c2 -> c1 + c2)
                         | otherwise   -> promoteT $ letT (extractT $ countVarRefT v)
                                                          (extractT $ countVarRefT v)
                                                          (\_ _ c1 c2 -> c1 + c2)

    ExprCL (Comp _ _ qs) | v `elem` compBoundVars qs -> promoteT $ compT (constT $ return 0)
                                                                         (extractT $ countVarRefT v)
                                                                         (\_ c1 c2 -> c1 + c2)
                         | otherwise                 -> promoteT $ compT (extractT $ countVarRefT v)
                                                                         (extractT $ countVarRefT v)
                                                                         (\_ c1 c2 -> c1 + c2)
    ExprCL Table{}                      -> return 0
    ExprCL Lit{}                        -> return 0

    ExprCL _                            -> allT (countVarRefT v)

    QualsCL (BindQ v' _ :* _) | v == v' -> childT QualsHead (countVarRefT v)
    QualsCL _                           -> allT (countVarRefT v)

    QualCL  _                           -> allT (countVarRefT v)

-- | Remove a let-binding that is not referenced.
unusedBindingR :: RewriteC CL
unusedBindingR = do
    Let _ x _ e2 <- promoteT idR
    0            <- childT LetBody $ countVarRefT x
    return $ inject e2

-- | Inline a let-binding that is only referenced once.
referencedOnceR :: RewriteC CL
referencedOnceR = do
    Let _ x e1 _ <- promoteT idR
    1            <- childT LetBody $ countVarRefT x

    -- We do not inline into comprehensions, but 'countVarRef' counts
    -- all occurences including those in comprehensions. For this
    -- reason, we check if the occurence was actually eliminated by
    -- inlining and fail otherwise.
    body'        <- childT LetBody (inlineBindingR x e1)
    0 <- constT (return body') >>> countVarRefT x
    return body'

simpleExpr :: Expr -> Bool
simpleExpr Table{} = True
simpleExpr Var{}   = True
simpleExpr _       = False

-- | Inline a let-binding that binds a simple expression.
simpleBindingR :: RewriteC CL
simpleBindingR = do
    Let _ x e1 _ <- promoteT idR
    guardM $ simpleExpr e1
    childR LetBody $ substR x e1

