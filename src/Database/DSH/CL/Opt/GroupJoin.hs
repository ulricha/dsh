{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}

-- FIXME TODO
-- * Redefine GroupJoin to include NestJoin
-- * Gradually merge aggregates into existing GroupJoin
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

import           Data.List.NonEmpty                    (NonEmpty ((:|)))
import qualified Data.List.NonEmpty                    as N

import           Database.DSH.Common.Lang
import           Database.DSH.Common.Nat
import           Database.DSH.Common.Pretty

import           Database.DSH.CL.Kure
import           Database.DSH.CL.Lang

import qualified Database.DSH.CL.Primitives            as P

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
groupjoinR = groupjoinQualR <+ groupjoinQualsR

groupjoinQualR :: RewriteC CL
groupjoinQualR = do
    e@(Comp ty h (S (BindQ x (NestJoinP _ p xs ys)))) <- promoteT idR
    (h', joinOp, _) <- groupjoinWorkerT h x p xs ys
    -- trace ("groupjoinqualR:\n" ++ pp e) $ return ()
    -- trace ("head:\n" ++ pp h') $ return ()
    -- trace ("joinOp:\n" ++ pp joinOp) $ return ()
    return $ inject $ Comp ty h' (S (BindQ x joinOp))

-- FIXME update type of x in qualifiers
-- FIXME make sure that there are no other occurences of x.2 in qualifiers.
groupjoinQualsR :: RewriteC CL
groupjoinQualsR = do
    e@(Comp ty h (BindQ x (NestJoinP _ p xs ys) :* qs)) <- promoteT idR
    (h', joinOp, xv') <- groupjoinWorkerT h x p xs ys
    qs'               <- constT (return $ inject qs) >>> substR x xv' >>> projectT
    trace ("groupjoinqualsR:\n" ++ pp e) $ return ()
    -- trace ("head:\n" ++ pp h') $ return ()
    trace ("joinOp:\n" ++ pp joinOp) $ return ()
    -- trace ("quals:\n" ++ pp qs') $ return ()
    return $ inject $ Comp ty h' (BindQ x joinOp :* qs')

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
    e@(GroupJoinP _ p1 (NE (a1 :| [])) (GroupJoinP _ p2 (NE (a2 :| [])) xs ys) ys') <- promoteT idR
    guardM $ ys == ys'

    guardM $ and $ N.zipWith (\c1 c2 -> leftCompatible (jcLeft c1) (jcLeft c2)
                                        && jcOp c1 == jcOp c2
                                        && jcRight c1 == jcRight c2)
                             (jpConjuncts p1)
                             (jpConjuncts p2)

    trace (pp e) $ return ()

    let xt = elemT $ typeOf xs
        a1t = aggType a1
        a2t = aggType a2
        gt = TupleT [xt, a2t, a1t]
        combinedJoin = GroupJoinP (ListT gt) p2 (NE (a2 :| [a1])) xs ys

    ga <- freshNameT []
    let gav = Var gt ga

    let h = P.pair (P.pair (P.fst gav) (P.snd gav)) (P.tupElem (Next (Next First)) gav)
    return $ inject $ P.singleGenComp h ga combinedJoin
