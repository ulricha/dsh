{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PatternSynonyms #-}

module Database.DSH.CL.Opt.AntiJoin
    ( antijoinR
    ) where

import           Control.Arrow
import           Control.Applicative
import           Data.List.NonEmpty         (NonEmpty ((:|)))
import           Data.Semigroup
import qualified Data.Traversable as T
import Data.List

import           Database.DSH.CL.Kure
import           Database.DSH.CL.Lang
import           Database.DSH.CL.Opt.Aux
import qualified Database.DSH.CL.Primitives as P
import           Database.DSH.Common.Lang

--------------------------------------------------------------------------------
-- Universal quantification with and without range predicates

-- | Turn universal quantification with range and quantifier predicates into an
-- antijoin. We use the classification of queries in Claussen et al.: Optimizing
-- Queries with Universal Quantification in Object-Oriented and
-- Object-Relational Databases (VLDB 1995).

pattern PAnd xs <- AppE1 _ (Prim1 And _) xs
pattern PNot e <- UnOp _ (SUBoolOp Not) e

negateRelOp :: BinRelOp -> BinRelOp
negateRelOp op = case op of
    Eq  -> NEq
    NEq -> Eq
    GtE -> Lt
    LtE -> Gt
    Lt  -> GtE
    Gt  -> LtE

-- | Quantifier predicates that reference inner and outer relation
-- appear negated on the antijoin.
quantifierPredicateT :: Ident 
                     -> Ident 
                     -> TransformC CL (NonEmpty (JoinConjunct JoinExpr))
quantifierPredicateT x y = readerT $ \q -> case q of
    -- If the quantifier predicate is already negated, take its
    -- non-negated form.
    ExprCL (PNot _) -> do
        conjs <- childT UnOpArg (joinConjunctsT x y)
        return conjs

    -- If the predicate is a simple relational operator, but
    -- non-negated, try to negate the operator itself.
    ExprCL (BinOp t (SBRelOp op) e1 e2) -> do
        let e' = BinOp t (SBRelOp $ negateRelOp op) e1 e2
        q' <- constT (return e') >>> splitJoinPredT x y
        return $ q' :| []
        
    _                          -> fail "can't handle predicate"


universalQualR :: RewriteC (NL Qual)
universalQualR = readerT $ \quals -> case quals of
    -- Special case: no range predicate
    -- [ ... | ..., x <- xs, and [ q | y <- ys ]]
    BindQ x xs :* (S (GuardQ (PAnd (Comp _ q (S (BindQ y ys)))))) -> do
        qPred <- constT (return q) >>> injectT >>> quantifierPredicateT x y
        return $ S $ BindQ x (P.antijoin xs ys $ JoinPred $ qPred)

    -- Special case: no range predicate
    -- [ ... | ..., x <- xs, and [ q | y <- ys ], ... ]
    BindQ x xs :* (GuardQ (PAnd (Comp _ q (S (BindQ y ys))))) :* qs -> do
        qPred <- constT (return q) >>> injectT >>> quantifierPredicateT x y
        return $ (BindQ x (P.antijoin xs ys $ JoinPred $ qPred)) :* qs

    -- [ ... | ..., x <- xs, and [ q | y <- ys, ps ], ... ]
    BindQ x xs :* GuardQ (PAnd (Comp _ q (BindQ y ys :* ps))) :* qs -> do
        antijoinGen <- mkUniversalRangeAntiJoinT (x, xs) (y, ys) ps q
        return $ antijoinGen :* qs

    -- [ ... | ..., x <- xs, and [ q | y <- ys, ps ]]
    BindQ x xs :* (S (GuardQ (PAnd (Comp _ q (BindQ y ys :* ps))))) -> do
        antijoinGen <- mkUniversalRangeAntiJoinT (x, xs) (y, ys) ps q
        return $ S $ antijoinGen
    _ -> fail "no and pattern"

mkUniversalRangeAntiJoinT :: (Ident, Expr) 
                     -> (Ident, Expr)
                     -> NL Qual
                     -> Expr
                     -> TransformC (NL Qual) Qual
mkUniversalRangeAntiJoinT (x, xs) (y, ys) ps q = do
    psExprs <- constT $ T.mapM fromGuard ps
    let psFVs = sort $ nub $ concatMap freeVars $ toList psExprs
        qFVs  = sort $ nub $ freeVars q

    let xy = sort [x, y]

    debugMsg $ show psFVs
    debugMsg $ show qFVs
    debugMsg $ show xy

    case (psFVs, qFVs) of
        -- Class 12: p(y), q(x, y)
        ([y'], qsvs@[_, _]) | y == y' && qsvs == xy -> do
            qPred <- constT (return q) >>> injectT >>> quantifierPredicateT x y
            mkClass12AntiJoinT (x, xs) (y, ys) psExprs (JoinPred qPred)

        -- Class 15: p(x, y), q(y)
        (psvs@[_, _], [y']) | psvs == xy && y == y' -> do
            psConjs <- constT (return psExprs) >>> mapT (splitJoinPredT x y)
            let psPred = JoinPred $ toNonEmpty psConjs
            mkClass15AntiJoinT (x, xs) (y, ys) psPred q

        -- Class 16: p(x, y), q(x, y)
        (psvs@[_, _], qsvs@[_, _]) | psvs == xy && qsvs == xy -> do
            psConjs <- constT (return psExprs) >>> mapT (splitJoinPredT x y)
            qPred   <- constT (return q) >>> injectT >>> quantifierPredicateT x y
            mkClass16AntiJoinT (x, xs) ys (toNonEmpty psConjs) qPred

        _ -> fail "FIXME"


mkClass12AntiJoinT :: (Ident, Expr)               -- ^ Generator variable and expression for the outer
                   -> (Ident, Expr)
                   -> NL Expr
                   -> JoinPredicate JoinExpr
                   -> TransformC (NL Qual) Qual
mkClass12AntiJoinT (x, xs) (y, ys) ps qs = do
    let yst = typeOf ys
        yt  = elemT yst

    -- [ y | y <- ys, ps ]
    let ys' = Comp yst (Var yt y) (BindQ y ys :* fmap GuardQ ps)

    -- xs ▷_ps [ y | y <- ys, not qs ]
    return $ BindQ x (P.antijoin xs ys' qs)

-- This rewrite implements plan 14 for Query Class 15 in Claussen et al.,
-- Optimizing Queries with Universal Quantification... (VLDB, 1995).  Class 15
-- contains queries in which the range predicate ranges over both relations,
-- i.e. x and y occur free. The quantifier predicate on the other hand ranges
-- only over the inner relation:
-- p(x, y), q(y)
mkClass15AntiJoinT :: (Ident, Expr)               -- ^ Generator variable and expression for the outer
                   -> (Ident, Expr)
                   -> JoinPredicate JoinExpr
                   -> Expr
                   -> TransformC (NL Qual) Qual
mkClass15AntiJoinT (x, xs) (y, ys) ps qs = do
    let yst = typeOf ys
        yt  = elemT yst

    -- [ y | y <- ys, not q ]
    let ys' = Comp yst (Var yt y) (BindQ y ys :* S (GuardQ $ P.not qs))

    -- xs ▷_not(qs) [ y | y <- ys, ps ]
    return $ BindQ x (P.antijoin xs ys' ps)

mkClass16AntiJoinT :: (Ident, Expr)
                   -> Expr
                   -> NonEmpty (JoinConjunct JoinExpr) 
                   -> NonEmpty (JoinConjunct JoinExpr)
                   -> TransformC (NL Qual) (Qual)
mkClass16AntiJoinT (x, xs) ys ps qs = do
    -- xs ▷_(p && not q) ys
    return $ BindQ x (P.antijoin xs ys $ JoinPred $ ps <> qs)

universalQualsR :: RewriteC (NL Qual)
universalQualsR = onetdR universalQualR

antijoinR :: RewriteC CL
antijoinR = do
    Comp _ _ _ <- promoteT idR
    childR CompQuals (promoteR universalQualsR)
