{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}

-- | Normalize patterns from source programs (not to be confused with
-- comprehension normalization)
module Database.DSH.CL.Opt.Normalize
  ( normalizeOnceR
  , normalizeExprR
  ) where

import           Control.Arrow
import qualified Data.Foldable                  as F
import           Data.Monoid
import qualified Data.Traversable               as T

import           Database.DSH.CL.Kure
import           Database.DSH.CL.Lang
import           Database.DSH.CL.Opt.Auxiliary
import qualified Database.DSH.CL.Primitives     as P
import           Database.DSH.Common.Lang
import           Database.DSH.Common.Kure

------------------------------------------------------------------
-- Simple normalization rewrites that are applied only at the start of
-- rewriting.

-- Rewrites that are expected to only match once in the beginning and whose
-- pattern should not occur due to subsequent rewrites.

-- | Split conjunctive predicates.
splitConjunctsR :: RewriteC (NL Qual)
splitConjunctsR = logR "normalize.splitconjunct" (splitR <+ splitEndR)
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
notExistsR = logR "normalize.notexists" $ promoteT $ readerT $ \e -> case e of
    -- No quantifier predicate:
    -- not (or [ true | y <- ys, qs ])
    -- =>
    -- and [ false | y <- ys, qs ]
    NotP (OrP (Comp ty TrueP ((y :<-: ys) :* qs))) ->
        return $ inject $ P.and $ Comp ty FalseP ((y :<-: ys) :* qs)

    -- Quantifier predicate, with range predicates
    -- not (or [ q | y <- ys, p1, ..., pn ])
    -- =>
    -- and [ not q | y <- ys, p1, ..., pn ]
    NotP (OrP (Comp t q (BindQ y ys :* ps))) ->
        return $ inject $ P.and $ Comp t (P.not q) (BindQ y ys :* ps)

    -- Without range predicates
    -- not (or [ q | y <- ys ])
    -- =>
    -- and [ not q | y <- ys ]
    NotP (OrP (Comp t q (S (BindQ y ys)))) ->
        return $ inject $ P.and $ Comp t (P.not q) (S $ BindQ y ys)

    _ -> fail "no match"

-- Normalization of null occurences
-- length xs == 0 => null xs
-- 0 == length xs => null xs
zeroLengthR :: RewriteC CL
zeroLengthR = logR "normalize.zerolength" $ promoteT $ readerT $ \e -> case e of
    EqP (LengthP xs) (Lit _ (ScalarV (IntV 0))) -> return $ inject $ P.null xs
    EqP (Lit _ (ScalarV (IntV 0))) (LengthP xs) -> return $ inject $ P.null xs
    _                                 -> fail "no match"

-- null [ _ | x <- xs, p1, p2, ... ]
-- => and [ not (p1 && p2 && ...) | x <- xs ]
comprehensionNullR :: RewriteC CL
comprehensionNullR = logR "normalize.compnull" $ do
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
notNullR = logR "normalize.notnull" $ do
    NotP (AndP (Comp _ (NotP p) (S (BindQ x xs)))) <- promoteT idR
    return $ inject $ P.or (Comp (ListT PBoolT) p (S (BindQ x xs)))

--------------------------------------------------------------------------------
-- Inline let bindings

-- | Count all occurences of an identifier for let-inlining.
countVarRefT :: Ident -> TransformC CL (Sum Int)
countVarRefT v = readerT $ \expr -> case expr of
    -- Occurence of the variable to be replaced
    ExprCL (Var _ n)
        | n == v                        -> return 1
        | otherwise                     -> return 0

    ExprCL (Let _ n _ _)
        | n == v                        -> childT LetBind (countVarRefT v)
        | otherwise                     -> allT (countVarRefT v)
    ExprCL (Comp _ _ qs)
        | v `elem` compBoundVars qs     -> childT CompQuals (countVarRefT v)
        | otherwise                     -> allT (countVarRefT v)
    ExprCL Table{}                      -> return 0
    ExprCL Lit{}                        -> return 0

    ExprCL _                            -> allT (countVarRefT v)

    QualsCL (BindQ v' _ :* _) | v == v' -> childT QualsHead (countVarRefT v)
    QualsCL _                           -> allT (countVarRefT v)

    QualCL  _                           -> allT (countVarRefT v)

-- | Remove a let-binding that is not referenced.
unusedBindingR :: RewriteC CL
unusedBindingR = logR "normalize.letunused" $ do
    Let _ x _ e2 <- promoteT idR
    0            <- childT LetBody $ countVarRefT x
    return $ inject e2

-- | Inline a let-binding that is only referenced once.
referencedOnceR :: RewriteC CL
referencedOnceR = logR "normalize.letonce" $ do
    Let _ x e1 e2 <- promoteT idR
    1            <- childT LetBody $ countVarRefT x
    substNoCompM x e1 e2 >>> injectT

simpleExpr :: Expr -> Bool
simpleExpr Table{}                 = True
simpleExpr Var{}                   = True
simpleExpr (AppE1 _ (TupElem _) e) = simpleExpr e
simpleExpr (BinOp _ _ e1 e2)       = simpleExpr e1 && simpleExpr e2
simpleExpr (UnOp _ _ e)            = simpleExpr e
simpleExpr _                       = False

-- | Inline a let-binding that binds a simple expression.
simpleBindingR :: RewriteC CL
simpleBindingR = logR "normalize.letsimple" $ do
    Let _ x e1 e2 <- promoteT idR
    guardM $ simpleExpr e1
    substM x e1 e2 >>> injectT
