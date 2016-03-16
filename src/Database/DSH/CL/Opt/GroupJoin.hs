{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}

-- FIXME TODO
-- * Use same infrastructure to introduce GroupAggr
-- * Special case: duplicate elimination -> CountDistinct

module Database.DSH.CL.Opt.GroupJoin
  ( groupjoinR
  , sidewaysR
  , mergeGroupjoinR
  ) where

import           Control.Arrow

import           Data.List
import           Data.List.NonEmpty             (NonEmpty ((:|)))
import qualified Data.List.NonEmpty             as N
import           Data.Semigroup                 ((<>))

import           Database.DSH.Common.Impossible
import           Database.DSH.Common.Lang
import           Database.DSH.Common.Nat

import           Database.DSH.CL.Kure
import           Database.DSH.CL.Lang

import qualified Database.DSH.CL.Primitives     as P

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

--------------------------------------------------------------------------------
-- Introduce GroupJoin operator for aggregates in the comprehension head or a
-- guard.

traverseGuardsT :: Ident -> TransformC CL a -> TransformC CL a
traverseGuardsT genName t = readerT $ \qs -> case qs of
    QualsCL (BindQ y _ :* _)
        | y == genName      -> fail "nestjoin generator name shadowed"
        | otherwise         -> childT QualsTail (traverseGuardsT genName t)
    QualsCL (GuardQ _ :* _) -> pathT [QualsHead, GuardQualExpr] t
                               <+ childT QualsTail (traverseGuardsT genName t)
    QualsCL (S (GuardQ _))  -> pathT [QualsSingleton, GuardQualExpr] t
    QualsCL (S (BindQ _ _)) -> fail "end of qualifier list"
    _                       -> fail "not a qualifier list"

-- | Merge a NestJoin operator and an aggregate into a GroupJoin.
groupjoinR :: RewriteC CL
groupjoinR = do
    Comp ty _ qs <- promoteT idR

    -- We need one NestJoin generator on a comprehension
    (x, p, xs, ys) <- case qs of
        S (BindQ x (NestJoinP _ p xs ys))  -> return (x, p, xs, ys)
        BindQ x (NestJoinP _ p xs ys) :* _ -> return (x, p, xs, ys)
        _                                  -> fail "no match"

    -- Search for an eligible aggregate in the comprehension head and guards.
    (aggPath, agg) <- childT CompHead (searchAggregatedGroupT x)
                      <+
                      pathT [CompQuals, QualsTail] (traverseGuardsT x (searchAggregatedGroupT x))

    let (joinOp, joinTy) = mkGroupJoin agg p xs ys
        xv'              = Var joinTy x

    localPath <- localizePathT aggPath

    -- Replace the aggregate with expression with x.2 (the aggregate produced by
    -- GroupJoin).
    Comp _ h' qs' <- pathR localPath (constT $ return $ inject $ P.snd xv') >>> projectT

    -- Update the type of the variable bound by the NestJoin/GroupJoin
    -- generator.
    h'' <- constT (return $ inject h') >>> substR x xv' >>> projectT
    qs'' <- constT (return $ inject qs') >>> substR x xv' >>> projectT

    case qs'' of
        BindQ _ _ :* qsr -> return $ inject $ Comp ty h'' (BindQ x joinOp :* qsr)
        S (BindQ _ _)    -> return $ inject $ Comp ty h'' (S (BindQ x joinOp))
        _                -> $impossible

-- | Construct a groupjoin operator for the given inputs and predicate. Return
-- the operator expression and its element type.
mkGroupJoin :: AggrApp -> JoinPredicate ScalarExpr -> Expr -> Expr -> (Expr, Type)
mkGroupJoin agg p xs ys =
    (GroupJoinP (ListT xt') p (NE $ pure agg) xs ys, xt')
  where
    xt  = elemT $ typeOf xs
    at  = aggType agg
    xt' = TupleT [xt, at]

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

--------------------------------------------------------------------------------
-- Merging of GroupJoin operators

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
    GroupJoinP _ p1 (NE (a1 :| [])) (GroupJoinP ty p2 (NE as) xs ys) ys' <- promoteT idR
    guardM $ ys == ys'

    guardM $ and $ N.zipWith (\c1 c2 -> leftCompatible (jcLeft c1) (jcLeft c2)
                                        && jcOp c1 == jcOp c2
                                        && jcRight c1 == jcRight c2)
                             (jpConjuncts p1)
                             (jpConjuncts p2)

    mergeExistingAggrR a1 as (elemT ty) p2 xs ys <+ mergeNewAggrR a1 as p2 xs ys

-- FIXME this will never fire because the input type annotations in the
-- aggregate expressions are not the same.
mergeExistingAggrR :: AggrApp -> N.NonEmpty AggrApp -> Type -> JoinPredicate ScalarExpr -> Expr -> Expr -> RewriteC CL
mergeExistingAggrR a as ty p xs ys = do
    Just aggIndex <- return $ elemIndex a $ N.toList as
    let combinedJoin = GroupJoinP (ListT ty) p (NE as) xs ys

    ga <- freshNameT []
    let gav = Var ty ga

    let h = P.pair (P.tuple $ map (\i -> P.tupElem (intIndex i) gav) [1..length as + 1])
                   (P.tupElem (intIndex $ aggIndex + 1) gav)
    return $ inject $ P.singleGenComp h ga combinedJoin

mergeNewAggrR :: AggrApp -> N.NonEmpty AggrApp -> JoinPredicate ScalarExpr -> Expr -> Expr -> RewriteC CL
mergeNewAggrR a as p xs ys = do
    let xt  = elemT $ typeOf xs
        a1t = aggType a
        ats = map aggType $ N.toList as
        gt  = TupleT $ xt : ats ++ [a1t]
        as' = as <> pure a
        combinedJoin = GroupJoinP (ListT gt) p (NE as') xs ys

    ga <- freshNameT []
    let gav = Var gt ga

    let h = P.pair (P.tuple $ map (\i -> P.tupElem (intIndex i) gav) [1..length as + 1])
                   (P.tupElem (intIndex $ length as + 2) gav)
    return $ inject $ P.singleGenComp h ga combinedJoin
