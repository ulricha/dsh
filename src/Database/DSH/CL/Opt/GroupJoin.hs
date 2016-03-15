{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}

-- FIXME TODO
-- * Search in guards for aggregates
-- * Use same infrastructure to introduce GroupAggr
-- * Special case: duplicate elimination -> CountDistinct

module Database.DSH.CL.Opt.GroupJoin
  ( groupjoinR
  , sidewaysR
  , mergeGroupjoinR
  ) where

import           Debug.Trace

import           Control.Arrow

import           Data.List.NonEmpty            (NonEmpty ((:|)))
import qualified Data.List.NonEmpty            as N
import           Data.Semigroup                ((<>))

import           Database.DSH.Common.Lang
import           Database.DSH.Common.Nat
import           Database.DSH.Common.Pretty

import           Database.DSH.CL.Kure
import           Database.DSH.CL.Lang

import qualified Database.DSH.CL.Primitives    as P

import           Database.DSH.CL.Opt.Auxiliary

-- | Rewrite the child expression of the aggregate into a scalar expression. The
-- identifier 'x' is the name bound by the outer comprehension.
--
-- The following forms can be rewritten:
--
-- @ x.2 @
-- @ [ f y | y <- x.2 ] @
toAggregateExprT :: Ident -> TransformC CL ScalarExpr
toAggregateExprT x =
    readerT $ \e -> case e of
        ExprCL (Comp _ _ (S (y :<-: TupSecondP _ (Var _ x')))) | x == x' ->
            childT CompHead $ promoteT (toScalarExpr y)
        ExprCL (TupSecondP t (Var _ x')) | x == x'                       ->
            return $ JInput t
        _                                                                ->
            fail "not an aggregate expression"

-- | Traverse though an expression and search for an aggregate that is eligible
-- for being merged into a NestJoin.
searchAggregatedGroupT :: Ident -> TransformC CL (PathC, AggrApp)
searchAggregatedGroupT x =
    readerT $ \e -> case e of
        ExprCL (AppE1 _ (Agg agg) _) ->
            (,) <$> (snocPathToPath <$> absPathT)
                <*> (AggrApp agg <$> childT AppE1Arg (toAggregateExprT x))
        ExprCL _      -> oneT $ searchAggregatedGroupT x
        _             -> fail "only traverse through expressions"

--------------------------------------------------------------------------------

groupjoinR :: RewriteC CL
groupjoinR = groupjoinFromHeadR

--------------------------------------------------------------------------------
-- Introduce GroupJoin operator for aggregates in the comprehension head.

groupjoinFromHeadR :: RewriteC CL
groupjoinFromHeadR = do
    Comp ty h qs <- promoteT idR

    -- We need one generator on a comprehension
    (x, p, xs, ys, qsr) <- case qs of
        S (BindQ x (NestJoinP _ p xs ys))     -> return (x, p, xs, ys, [])
        BindQ x (NestJoinP _ p xs ys) :* qsr  -> return (x, p, xs, ys, toList qsr)
        _                                     -> fail "no match"

    (h', joinOp, xv') <- groupjoinWorkerT h x p xs ys

    -- In the outer comprehension's qualifier list, x is replaced by
    -- the first pair component of the join result.
    qsr' <- constT (return $ map inject qsr)
            >>> mapT (substR x xv')
            >>> mapT projectT

    return $ inject $ Comp ty h' (fromListSafe (BindQ x joinOp) qsr')

-- FIXME make sure that there are no other occurences of x.2 in the head.
groupjoinWorkerT :: Expr
                 -> Ident
                 -> JoinPredicate ScalarExpr
                 -> Expr
                 -> Expr
                 -> TransformC CL (Expr, Expr, Expr)
groupjoinWorkerT h x p xs ys = do
    -- Search for an aggregate applied to the groups that are produced by
    -- NestJoin.
    (aggPath, agg) <- searchAggregatedGroupT x
    headPath <- drop 1 <$> localizePathT aggPath

    -- Type of the GroupJoin result: xs :: [a], ys :: [b] => [(a, p(b))]
    let xt  = elemT $ typeOf xs
        at  = aggType agg
        xt' = TupleT [xt, at]
        xv' = Var xt' x
    let joinOp = AppE2 (ListT xt') (GroupJoin p (NE $ pure agg)) xs ys

    -- In the head expression, update the type of the generator variable. Then,
    -- replace the aggregate with a reference to the aggregate computed by the
    -- GroupJoin.
    h' <- constT (return $ inject h)
              >>> substR x xv'
              >>> pathR headPath (constT $ return $ inject $ P.snd xv')
              >>> projectT
    return (h', joinOp, xv')

--------------------------------------------------------------------------------
-- Introduce GroupJoin operator for aggregates in a comprehension guard.

--------------------------------------------------------------------------------

-- | Side-ways information passing to pre-filter the left GroupJoin input in a
-- GroupJoin-NestJoin combination.
--
-- Basic idea: Execute the GroupJoin only for those elements of ys that will
-- actually find a join partner in the NestJoin.
sidewaysR :: RewriteC CL
sidewaysR = do
    NestJoinP ty1 p1 xs (GroupJoinP ty2 p2 as ys zs) <- promoteT idR
    JoinConjunct c1 Eq c2 :| [] <- return $ jpConjuncts p1
    let semiPred = JoinPred $ JoinConjunct c2 Eq c1 :| []
    return $ inject $ NestJoinP ty1 p1 xs (GroupJoinP ty2 p2 as (SemiJoinP (typeOf ys) semiPred ys xs) zs)

-- | Check whether the join predicates of two stacked GroupJoins are compatible
-- for merging. They are compatible if the predicate of the topmost join refers
-- to the first tuple component of the left input and they are otherwise
-- identical.
leftCompatible :: ScalarExpr -> ScalarExpr -> Bool
leftCompatible (JBinOp _ op e1 e2) (JBinOp _ op' e1' e2') =
    op == op' && leftCompatible e1 e1' && leftCompatible e2 e2'
leftCompatible (JUnOp _ op e) (JUnOp _ op' e') =
    op == op' && leftCompatible e e'
leftCompatible (JLit _ v) (JLit _ v') =
    v == v'
leftCompatible (JTupElem _ First JInput{}) (JInput _) = True
leftCompatible (JTupElem _ n e) (JTupElem _ n' e') =
    n == n' && leftCompatible e e'
leftCompatible _ _ = False

-- | Merge two group joins into one if their join predicates and left inputs are
-- compatible.
mergeGroupjoinR :: RewriteC CL
mergeGroupjoinR = do
    e@(GroupJoinP _ p1 (NE (a1 :| [])) (GroupJoinP _ p2 (NE as) xs ys) ys') <- promoteT idR
    guardM $ ys == ys'

    guardM $ and $ N.zipWith (\c1 c2 -> leftCompatible (jcLeft c1) (jcLeft c2)
                                        && jcOp c1 == jcOp c2
                                        && jcRight c1 == jcRight c2)
                             (jpConjuncts p1)
                             (jpConjuncts p2)

    trace (pp e) $ return ()

    let xt  = elemT $ typeOf xs
        a1t = aggType a1
        ats = map aggType $ N.toList as
        gt  = TupleT $ xt : ats ++ [a1t]
        as' = as <> pure a1
        combinedJoin = GroupJoinP (ListT gt) p2 (NE as') xs ys

    ga <- freshNameT []
    let gav = Var gt ga

    let h = P.pair (P.tuple $ map (\i -> P.tupElem (intIndex i) gav) [1..length as + 1])
                   (P.tupElem (intIndex $ length as + 2) gav)
    return $ inject $ P.singleGenComp h ga combinedJoin
