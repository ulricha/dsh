{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PatternSynonyms #-}

module Database.DSH.CL.Opt.AntiJoin
    ( antijoinR
    ) where

import           Control.Arrow
import           Data.List.NonEmpty         (NonEmpty ((:|)))
import qualified Data.List.NonEmpty as NL
import           Data.Semigroup
import qualified Data.Traversable as T
import           Data.List

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
-- appear negated on the antijoin. The transform results in a
-- non-empty list of join conjuncts extracted from the negated
-- quantifier predicate. In addition, it returns a (possibly empty)
-- list of conjuncts that only reference the inner variable and can be
-- evaluated on the inner source.
quantifierPredicateT :: Ident 
                     -> Ident 
                     -> TransformC CL (NonEmpty (JoinConjunct JoinExpr), [Expr])
quantifierPredicateT x y = readerT $ \q -> case q of
    -- If the quantifier predicate is already negated, take its
    -- non-negated form.
    ExprCL (PNot _) -> do
        conjs <- childT UnOpArg conjunctsT

        -- Separate predicate parts that only depend on the inner
        -- variable.
        let (nonCorrExprs, corrExprs) = partition (\e -> freeVars e == [y]) $ NL.toList conjs

        -- Note: We can't be sure that there actually is at least one
        -- predicate that is correlated. As the caller only checks
        -- that x and y occur in the combined predicate, we might run
        -- into the following freak case: p1 x && p2 y. In this case,
        -- fail the rewrite completely.
        corrExprs' <- case corrExprs of
                          c : cs -> return $ c :| cs
                          []     -> fail "no correlated predicates for the join"

        corrPreds <- constT (return corrExprs') >>> mapT (splitJoinPredT x y)
        return (corrPreds, nonCorrExprs)

    -- If the predicate is a simple relational operator, but
    -- non-negated, try to negate the operator itself.
    ExprCL (BinOp t (SBRelOp op) e1 e2) -> do
        let e' = BinOp t (SBRelOp $ negateRelOp op) e1 e2
        q' <- constT (return e') >>> splitJoinPredT x y
        return (q' :| [], [])
        
    _                          -> fail "can't handle predicate"

mkUniversalQuantOnlyAntiJoinT :: (Ident, Expr) 
                              -> (Ident, Expr) 
                              -> Expr 
                              -> TransformC (NL Qual) Qual
mkUniversalQuantOnlyAntiJoinT (x, xs) (y, ys) q = do
    (qPred, nonCorrPreds) <- constT (return q) >>> injectT >>> quantifierPredicateT x y
    
    let yst = typeOf ys
        yt  = elemT yst

    let innerQuals = case nonCorrPreds of
                         p : ps -> BindQ y ys :* fmap GuardQ (fromListSafe p ps)
                         []     -> S $ BindQ y ys

    -- Filter the inner source with the range
    -- predicates. Additionally, filter it with the non-correlated
    -- predicates extracted from the quantifier predicate.
    -- [ y | y <- ys, ps ++ nonCorrPreds ]
    let ys' = Comp yst (Var yt y) innerQuals

    return $ BindQ x (P.antijoin xs ys' $ JoinPred $ qPred)

universalQualR :: RewriteC (NL Qual)
universalQualR = readerT $ \quals -> case quals of
    -- Special case: no range predicate
    -- [ ... | ..., x <- xs, and [ q | y <- ys ]]
    BindQ x xs :* (S (GuardQ (PAnd (Comp _ q (S (BindQ y ys)))))) -> do
        antijoinGen <- mkUniversalQuantOnlyAntiJoinT (x, xs) (y, ys) q
        return $ S antijoinGen

    -- Special case: no range predicate
    -- [ ... | ..., x <- xs, and [ q | y <- ys ], ... ]
    BindQ x xs :* (GuardQ (PAnd (Comp _ q (S (BindQ y ys))))) :* qs -> do
        antijoinGen <- mkUniversalQuantOnlyAntiJoinT (x, xs) (y, ys) q
        return $ antijoinGen :* qs

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
            (qPred, nonCorrPreds) <- constT (return q) >>> injectT >>> quantifierPredicateT x y
            mkClass12AntiJoinT (x, xs) (y, ys) psExprs (JoinPred qPred) nonCorrPreds

        -- Class 15: p(x, y), q(y)
        (psvs@[_, _], [y']) | psvs == xy && y == y' -> do
            psConjs <- constT (return psExprs) >>> mapT (splitJoinPredT x y)
            let psPred = JoinPred $ toNonEmpty psConjs
            mkClass15AntiJoinT (x, xs) (y, ys) psPred q

        -- Class 16: p(x, y), q(x, y)
        (psvs@[_, _], qsvs@[_, _]) | psvs == xy && qsvs == xy -> do
            psConjs <- constT (return psExprs) >>> mapT (splitJoinPredT x y)

            -- Even if q itself references x and y, there might be
            -- parts of the predicate (conjuncts) which only reference
            -- y. These parts can (and should) be evaluated on ys.
            (qPred, nonCorrPreds) <- constT (return q) >>> injectT >>> quantifierPredicateT x y

            mkClass16AntiJoinT (x, xs) (y, ys) (toNonEmpty psConjs) qPred nonCorrPreds

        _ -> fail "FIXME"


mkClass12AntiJoinT :: (Ident, Expr)               -- ^ Generator variable and expression for the outer
                   -> (Ident, Expr)
                   -> NL Expr
                   -> JoinPredicate JoinExpr
                   -> [Expr]
                   -> TransformC (NL Qual) Qual
mkClass12AntiJoinT (x, xs) (y, ys) ps qs nonCorrPreds = do
    let yst = typeOf ys
        yt  = elemT yst

    -- Filter the inner source with the range
    -- predicates. Additionally, filter it with the non-correlated
    -- predicates extracted from the quantifier predicate.  
    -- [ y | y <- ys, ps ++ nonCorrPreds ]
    let innerPreds = case nonCorrPreds of
                         c : cs -> appendNL ps (fromListSafe c cs)
                         []     -> ps

    let ys' = Comp yst (Var yt y) (BindQ y ys :* fmap GuardQ innerPreds)

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
                   -> (Ident, Expr)
                   -> NonEmpty (JoinConjunct JoinExpr) 
                   -> NonEmpty (JoinConjunct JoinExpr)
                   -> [Expr]
                   -> TransformC (NL Qual) (Qual)
mkClass16AntiJoinT (x, xs) (y, ys) ps qs nonCorrPreds = do
    -- Prepare a comprehension that filters the inner input by the
    -- non-correlated predicates extracted from the quantifier
    -- predicate.
    let yst = typeOf ys
        yt  = elemT yst

    let ys' = case nonCorrPreds of
                  c : cs -> let quals = BindQ y ys :* fmap GuardQ (fromListSafe c cs)
                            in Comp yst (Var yt y) quals
                  []     -> ys

    -- xs ▷_(p && not q) ys
    return $ BindQ x (P.antijoin xs ys' $ JoinPred $ ps <> qs)

universalQualsR :: RewriteC (NL Qual)
universalQualsR = onetdR universalQualR

antijoinR :: RewriteC CL
antijoinR = do
    Comp _ _ _ <- promoteT idR
    childR CompQuals (promoteR universalQualsR)
