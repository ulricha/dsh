{-# LANGUAGE TemplateHaskell #-}

-- | Push filtering join operators (i.e. SemiJoin, AntiJoin) into the input of
-- other operators. The goal is to reduce cardinality as early as possible.
--
-- FIXME Consider other operators than Sort and NestJoin for pushing through.
-- ThetaJoin should work if the filtering join refers only to one of the
-- ThetaJoin inputs. Possibly, Group is eligible too (not sure about this).
module Database.DSH.CL.Opt.JoinPushdown
    ( joinPushdownR
    ) where

import           Control.Arrow
import qualified Data.List.NonEmpty              as N

import           Database.DSH.CL.Kure
import           Database.DSH.CL.Lang
import           Database.DSH.CL.Opt.Auxiliary
import           Database.DSH.CL.Opt.ProjectionPullup
import           Database.DSH.CL.Opt.PartialEval
import           Database.DSH.Common.Impossible
import           Database.DSH.Common.Lang
import           Database.DSH.Common.Nat

updatePredicateLeft :: N.NonEmpty e -> JoinPredicate e -> JoinPredicate e
updatePredicateLeft leftExprs p =
    p { jpConjuncts = N.zipWith merge leftExprs (jpConjuncts p) }
  where
    merge e c = c { jcLeft = e }


--------------------------------------------------------------------------------
-- Push filtering joins into nesting operators

-- | In a join expression, rewrite references to the first tuple element of the
-- input into direct references to the input. This is necessary when pushing
-- joins into inputs of other tupling join operators.
--
-- FIXME This rewrite should be integrated into the KURE-based framework for CL
-- rewrites.
untuplifyJoinPredLeft :: JoinPredicate ScalarExpr -> JoinPredicate ScalarExpr
untuplifyJoinPredLeft (JoinPred cs) = JoinPred $ fmap updateConjunct cs
  where
    updateConjunct jc = JoinConjunct (untuplifyScalarExpr (jcLeft jc)) (jcOp jc) (jcRight jc)

-- | If the left input of a filtering join is a NestJoin operator, push the join
-- into the left NestJoin input to reduce the cardinality before sorting.
--
-- In principle, we need to check whether the predicate of the filtering join
-- refers only to the first component of the tuples produced by NestJoin.
-- However, we know that the second tuple component has a list type and there is
-- no way that a list can occur in a join predicate.
--
-- Informally, the rewrite is correct because NestJoin produces one tuple for
-- each tuple from its left input. Whether these tuples are filtered before or
-- after is not relevant. Also, both NestJoin and SemiJoin keep the order of
-- their left input.
pushFilterjoinNestjoinR :: RewriteC CL
pushFilterjoinNestjoinR = do
    AppE2 ty joinOp (NestJoinP _ predNest xs ys) zs <- promoteT idR
    (joinConst, joinPred) <- isFilteringJoin joinOp
    -- Rewrite the join predicate to refer to the complete input, not only to
    -- its first tuple component. This is necessary because we are below the
    -- tupling caused by the NestJoin.
    let joinPred' = untuplifyJoinPredLeft joinPred
    return $ inject $ NestJoinP ty predNest (AppE2 (typeOf xs) (joinConst joinPred') xs zs) ys

firstOnlyJoinPred :: JoinPredicate ScalarExpr -> Bool
firstOnlyJoinPred p = all firstOnly $ jcLeft <$> jpConjuncts p

-- | If the left input of a filtering join is a GroupJoin operator, push the
-- join into the left NestJoin input to reduce the cardinality before sorting.
-- For this rewrite to work, we have to check whether the filtering join refers
-- only to the left component of the pairs produced by the GroupJoin.
--
-- Informally, the rewrite is correct because NestJoin produces one tuple for
-- each tuple from its left input. Whether these tuples are filtered before or
-- after is not relevant. Also, both NestJoin and SemiJoin keep the order of
-- their left input.
pushFilterjoinGroupJoinR :: RewriteC CL
pushFilterjoinGroupJoinR = do
    AppE2 ty joinOp (GroupJoinP _ predGroup as xs ys) zs <- promoteT idR
    (joinConst, joinPred) <- isFilteringJoin joinOp

    -- Check whether the filtering join predicate refers only to the left side
    -- of the GroupJoin.
    guardM $ firstOnlyJoinPred joinPred

    -- Rewrite the join predicate to refer to the complete input, not only to
    -- its first tuple component. This is necessary because we are below the
    -- tupling caused by the GroupJoin.
    let joinPred' = untuplifyJoinPredLeft joinPred
    return $ inject $ GroupJoinP ty predGroup as (AppE2 (typeOf xs) (joinConst joinPred') xs zs) ys

-- | If the left input of a filtering join is a NestProduct operator, push the join
-- into the left NestProduct input to reduce the cardinality before sorting.
--
-- In principle, we need to check whether the predicate of the filtering join
-- refers only to the first component of the tuples produced by NestProduct.
-- However, we know that the second tuple component has a list type and there is
-- no way that a list can occur in a join predicate.
--
-- Informally, the rewrite is correct because NestProduct produces one tuple for
-- each tuple from its left input. Whether these tuples are filtered before or
-- after is not relevant. Also, both NestProduct and SemiJoin keep the order of
-- their left input.
pushFilterjoinNestproductR :: RewriteC CL
pushFilterjoinNestproductR = do
    AppE2 ty joinOp (NestProductP _ xs ys) zs <- promoteT idR
    (joinConst, joinPred) <- isFilteringJoin joinOp
    -- Rewrite the join predicate to refer to the complete input, not only to
    -- its first tuple component. This is necessary because we are below the
    -- tupling caused by the NestJoin.
    let joinPred' = untuplifyJoinPredLeft joinPred
    return $ inject $ NestProductP ty (AppE2 (typeOf xs) (joinConst joinPred') xs zs) ys

--------------------------------------------------------------------------------
-- Push filtering joins into Sort operators

-- | In a join expression, turn references to the input into references to the
-- first tuple component of the input. The first argument provides the new pair
-- type of the input. This rewrite is necessary when pushing filtering joins
-- into the input of a sort operator.
--
-- Note: This is *not* the inverse of 'untuplifyJoinPredLeft'!
--
-- FIXME Should be integrated into the KURE-based framework.
tuplifyScalarExpr :: (Type, Type) -> JoinPredicate ScalarExpr -> JoinPredicate ScalarExpr
tuplifyScalarExpr (t1, t2) (JoinPred cs) = JoinPred $ fmap updateConjunct cs
  where
    updateConjunct jc = JoinConjunct (descend (jcLeft jc)) (jcOp jc) (jcRight jc)

    descend (JBinOp ty op e1 e2)                         = JBinOp ty op (descend e1) (descend e2)
    descend (JUnOp ty op e)                              = JUnOp ty op (descend e)
    descend (JTupElem ty idx e)                          = JTupElem ty idx (descend e)
    descend (JLit ty val)                                = JLit ty val
    descend (JInput _)                                   = JTupElem t1 First (JInput (TupleT [t1, t2]))

-- | If the left input of a filtering join is a Sort operator, push the join
-- into the Sort input to reduce the cardinality before sorting.
--
-- Note that we have to rewrite the join predicate because the Sort input tuples
-- the actual tuples with the sorting key.
--
-- @
-- SemiJoin{ f(I) == ... && ... } (Sort xs) ys
-- =>
-- Sort (SemiJoin { f(I.1) == ... && ... } xs ys)
-- @
--
-- Informally, the rewrite is correct because SemiJoin keeps the order of its
-- left input. Therefore, it does not change the order produced by Sort. Also,
-- it does not change the order of the Sort input. Sorting keys are computed
-- individually for tuples. Therefore, tuples can be removed from the Sort input
-- and the sorting key of the remaining tuples (and thus their position in the
-- output) will not change.
pushFilterjoinSortR :: RewriteC CL
pushFilterjoinSortR = do
    AppE2 ty joinOp (SortP _ xs) ys <- promoteT idR
    (joinConst, joinPred) <- isFilteringJoin joinOp

    let sortInputType = case typeOf xs of
            TupleT [t1, t2] -> (t1, t2)
            _               -> $impossible

    -- Rewrite the join predicate to refer only to the first tuple component of
    -- the sort input. The second tuple component is the sorting key which is
    -- eliminated after sorting.
    let joinPred' = tuplifyScalarExpr sortInputType joinPred

    return $ inject $ SortP ty (AppE2 (typeOf xs) (joinConst joinPred') xs ys)

--------------------------------------------------------------------------------

pushThroughRewritesR :: RewriteC CL
pushThroughRewritesR = pushFilterjoinNestjoinR
                       <+ pushFilterjoinSortR
                       <+ pushFilterjoinNestproductR
                       <+ pushFilterjoinGroupJoinR

joinPushdownR :: RewriteC CL
joinPushdownR =
    readerT $ \cl -> case cl of
        ExprCL AppE2{} -> (pullFromFilterJoinR >>> anytdR pushThroughRewritesR)
                          <+ pushThroughRewritesR
        _              -> fail "can't apply join pushdown rules"
