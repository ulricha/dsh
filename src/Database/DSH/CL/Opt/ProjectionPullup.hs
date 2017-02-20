{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE ScopedTypeVariables   #-}

-- FIXME TODO
-- * Pull projections from other operator inputs: joins, number, ...
-- * Pull projections if there are guards on the comprehension (the guards stay
--   below of course)

-- | Pull projections (i.e. single-generator comprehensions without joins) from
-- the input of certain operators. The primary goal is to normalize operator
-- trees so that operators are directly adjacent without interfering
-- comprehensions. As a side benefit, pulling projections should enable partial
-- evaluation (e.g. tuple construction/access fusion).
module Database.DSH.CL.Opt.ProjectionPullup
  ( pullProjectionR
  , pullFromFilterJoinR
  ) where

import           Control.Arrow

import qualified Data.List.NonEmpty              as N

import           Database.DSH.Common.Lang
import           Database.DSH.Common.Kure

import           Database.DSH.CL.Kure
import           Database.DSH.CL.Lang
import           Database.DSH.CL.Opt.Auxiliary
import           Database.DSH.CL.Opt.PartialEval
import qualified Database.DSH.CL.Primitives      as P

pullProjectionR :: RewriteC CL
pullProjectionR = logR "projectionpu.nestjoin.right" pullFromNestjoinRightR

-- | Pull a projection (i.e. a single-generator comprehension without guards)
-- from the right input of a NestJoin.
--
-- @
-- nestjoin{p} xs [ f y | y <- ys ]
-- =>
-- [ (x.1, [ (y.1, f[y.2/y]) | y <- x.2 ])
-- | x <- nestjoin{p} xs ys
-- ]
-- @
--
-- where x is fresh and p' is the predicate p with f inlined into the right
-- sides.
pullFromNestjoinRightR :: RewriteC CL
pullFromNestjoinRightR = do
    NestJoinP ty p xs (Comp _ h (S (y :<-: ys))) <- promoteT idR

    -- Tuple type of the pushed down NestJoin
    let xt = elemT $ typeOf xs
        yt = elemT $ typeOf ys
        njty = TupleT [xt, ListT (TupleT [xt, yt])]

    -- Inline the comprehension head into all right sides of the join predicate
    p' <- inlineJoinPredRightT h y p

    let nestJoin = NestJoinP (ListT njty) p' xs ys

    x <- freshNameT [y]
    let xv = Var njty x

    let yv = Var (TupleT [xt, yt]) y

    h' <- substM y (P.snd yv) h

    -- The inner comprehension that updates the nested components of the
    -- NestJoin result.
    let innerHead = P.tuple [P.fst yv, h']
    let innerComp = Comp (ListT $ typeOf innerHead) innerHead (S (y :<-: P.snd xv))

    -- The outer comprehension surrounding the NestJoin.
    let topHead = P.tuple [ P.fst xv, innerComp ]
    return $ inject $ Comp ty topHead (S (x :<-: nestJoin))

--------------------------------------------------------------------------------

-- | Pull a comprehension from the left input of a filtering join if the
-- comprehension has only one generator.
--
-- This rewrite helps in pushing filtering joins (semijoin, antijoin) as far
-- down as possible. The goal is to have the filtering join directly atop an
-- operator through which it can be pushed. The comprehension would be in the
-- way.
--
--    semijoin{ f(I) == ... && ... } [ g x | x <- xs, p1, ..., pn ] ys
-- => [ g x | x <- semijoin{ f(g(I)) == ... && ... } xs ys, p1, ..., pn ]
--
-- Note that this rewrite must not be used unconditionally. In contrast to other
-- projection pullup rewrites, we pull the comprehension including guards. If
-- the comprehension has guards, those guards would in turn be pushed into the
-- semijoin input by rewrites in 'PredPushdown'. This would lead to a rewrite
-- loop. However, the rewrite is safe as a preparation for rewrites that push
-- the filtering join further into other operators.
pullFromFilterJoinR :: RewriteC CL
pullFromFilterJoinR = logR "projectionpu.filterjoin" $ do
    AppE2 ty joinOp (Comp _ h (BindQ x xs :* qs)) ys <- promoteT idR
    (joinConst, joinPred) <- isFilteringJoin joinOp
    guardM $ all isGuard qs
    joinPred' <- inlineJoinPredLeftT h x joinPred

    let e' = Comp ty h (BindQ x (AppE2 (typeOf xs) (joinConst joinPred') xs ys) :* qs)
    return $ inject e'

--------------------------------------------------------------------------------
-- Inlining into join predicates

updatePredicateLeft :: N.NonEmpty e -> JoinPredicate e -> JoinPredicate e
updatePredicateLeft leftExprs p =
    p { jpConjuncts = N.zipWith merge leftExprs (jpConjuncts p) }
  where
    merge e c = c { jcLeft = e }

inlineJoinPredLeftT :: Expr -> Ident -> JoinPredicate ScalarExpr -> TransformC CL (JoinPredicate ScalarExpr)
inlineJoinPredLeftT e x joinPred = do
    -- Extract all left join expressions and turn them into regular expressions
    predInputName <- freshNameT []
    let leftPreds = fmap (fromScalarExpr predInputName . jcLeft) $ jpConjuncts joinPred

    -- Inline the head expression into the join predicate
    scopeNames <- inScopeNamesT
    let inlinedPreds = fmap (inject . substE scopeNames predInputName e) leftPreds

    -- Apply partial evaluation to the inlined predicate. This should increase
    -- the chance of being able to rewrite the inlined predicate back into a
    -- join predicate. The head expression that we inlined might have referred
    -- to expressions that we can't turn into join predicates. Partial
    -- evaluation (especially tuple fusion) should eliminate those.
    evalPreds     <- constT (return inlinedPreds) >>> mapT (tryR $ repeatR $ anybuR partialEvalNoLogR)

    -- Turn the join predicate back into a 'ScalarExpr'. If the inlined predicate
    -- can't be transformed, the complete rewrite will fail.
    leftPreds'    <- constT (return evalPreds) >>> mapT (promoteT $ toScalarExprT x)
    return $ updatePredicateLeft leftPreds' joinPred

updatePredicateRight :: N.NonEmpty e -> JoinPredicate e -> JoinPredicate e
updatePredicateRight rightExprs p =
    p { jpConjuncts = N.zipWith merge rightExprs (jpConjuncts p) }
  where
    merge e c = c { jcRight = e }

inlineJoinPredRightT :: Expr -> Ident -> JoinPredicate ScalarExpr -> TransformC CL (JoinPredicate ScalarExpr)
inlineJoinPredRightT e x joinPred = do
    -- Extract all right join expressions and turn them into regular expressions
    predInputName  <- freshNameT []
    let rightPreds = fmap (fromScalarExpr predInputName . jcRight) $ jpConjuncts joinPred

    -- Inline the head expression into the join predicate
    scopeNames <- inScopeNamesT
    let inlinedPreds = fmap (inject . substE scopeNames predInputName e) rightPreds

    -- Apply partial evaluation to the inlined predicate. This should increase
    -- the chance of being able to rewrite the inlined predicate back into a
    -- join predicate. The head expression that we inlined might have referred
    -- to expressions that we can't turn into join predicates. Partial
    -- evaluation (especially tuple fusion) should eliminate those.
    evalPreds     <- constT (return inlinedPreds) >>> mapT (tryR $ repeatR $ anybuR partialEvalNoLogR)

    -- Turn the join predicate back into a 'ScalarExpr'. If the inlined predicate
    -- can't be transformed, the complete rewrite will fail.
    rightPreds'    <- constT (return evalPreds) >>> mapT (promoteT $ toScalarExprT x)
    return $ updatePredicateRight rightPreds' joinPred
