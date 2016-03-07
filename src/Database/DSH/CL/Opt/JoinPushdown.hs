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
import           Database.DSH.CL.Opt.PartialEval
import           Database.DSH.Common.Impossible
import           Database.DSH.Common.Lang
import           Database.DSH.Common.Nat

updatePredicateLeft :: N.NonEmpty e -> JoinPredicate e -> JoinPredicate e
updatePredicateLeft leftExprs p =
    p { jpConjuncts = N.zipWith merge leftExprs (jpConjuncts p) }
  where
    merge e c = c { jcLeft = e }

-- | Push a semijoin into a comprehension in its left input if the comprehension
-- has only one generator.
--
-- This rewrite helps in pushing filtering joins (semijoin, antijoin) as far
-- down as possible.
--
--    semijoin{ f(I) == ... && ... } [ g x | x <- xs, p1, ..., pn ] ys
-- => [ g x | x <- semijoin{ f(g(I)) == ... && ... } xs ys, p1, ..., pn ]
--
-- Note that this rewrite must not be used unconditionally. If the comprehension
-- has guards, those guards would in turn be pushed into the semijoin input by
-- rewrites in 'PredPushdown'. This would lead to a rewrite loop. However, the
-- rewrite is safe as a preparation for rewrites that push the filtering join
-- further into other operators.
pushFilterjoinCompR :: RewriteC CL
pushFilterjoinCompR = do
    AppE2 ty joinOp (Comp _ h (BindQ x xs :* qs)) ys <- promoteT idR
    (joinConst, joinPred) <- isFilteringJoin joinOp
    guardM $ all isGuard qs

    -- Extract all left join expressions and turn them into regular expressions
    predInputName <- freshNameT []
    leftPreds     <- mapM (fromScalarExpr predInputName . jcLeft) $ jpConjuncts joinPred

    -- Inline the head expression into the join predicate
    inlinedPreds  <- constT (return leftPreds)
                     >>> mapT (extractT $ substR predInputName h)

    -- Apply partial evaluation to the inlined predicate. This should increase
    -- the chance of being able to rewrite the inlined predicate back into a
    -- join predicate. The head expression that we inlined might have referred
    -- to expressions that we can't turn into join predicates. Partial
    -- evaluation (especially tuple fusion) should eliminate those.
    evalPreds     <- constT (return inlinedPreds) >>> mapT (tryR partialEvalR)

    -- Turn the join predicate back into a 'ScalarExpr'. If the inlined predicate
    -- can't be transformed, the complete rewrite will fail.
    leftPreds'    <- constT (return evalPreds) >>> mapT (promoteT $ toScalarExpr x)
    let joinPred' = updatePredicateLeft leftPreds' joinPred

    let e' = Comp ty h (BindQ x (AppE2 (typeOf xs) (joinConst joinPred') xs ys) :* qs)
    return $ inject e'

--------------------------------------------------------------------------------
-- Push filtering joins into nesting operators

-- | In a join expression, rewrite references to the first tuple element of the
-- input into direct references to the input. This is necessary when pushing
-- joins into inputs of other tupling join operators.
--
-- FIXME This rewrite should be integrated into the KURE-based framework for CL rewrites.
untuplifyScalarExpr :: JoinPredicate ScalarExpr -> JoinPredicate ScalarExpr
untuplifyScalarExpr (JoinPred cs) = JoinPred $ fmap updateConjunct cs
  where
    updateConjunct jc = JoinConjunct (descend (jcLeft jc)) (jcOp jc) (jcRight jc)

    descend (JBinOp ty op e1 e2)                         = JBinOp ty op (descend e1) (descend e2)
    descend (JUnOp ty op e)                              = JUnOp ty op (descend e)
    descend (JTupElem _ First (JInput (TupleT [t1, _]))) = JInput t1
    descend (JTupElem _ _ (JInput _))                    = $impossible
    descend (JTupElem ty idx e)                          = JTupElem ty idx (descend e)
    descend (JLit ty val)                                = JLit ty val
    descend (JInput _)                                   = $impossible

isFilteringJoin :: Monad m => Prim2 -> m (JoinPredicate ScalarExpr -> Prim2, JoinPredicate ScalarExpr)
isFilteringJoin joinOp =
    case joinOp of
        SemiJoin p -> return (SemiJoin, p)
        AntiJoin p -> return (AntiJoin, p)
        _          -> fail "not a pushable join operator"

-- | If the left input of a filtering join is a NestJoin operator, push the join
-- into the left NestJoin input to reduce the cardinality before sorting.
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
    let joinPred' = untuplifyScalarExpr joinPred
    return $ inject $ NestJoinP ty predNest (AppE2 (typeOf xs) (joinConst joinPred') xs zs) ys

-- | If the left input of a filtering join is a NestProduct operator, push the join
-- into the left NestProduct input to reduce the cardinality before sorting.
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
    let joinPred' = untuplifyScalarExpr joinPred
    return $ inject $ NestProductP ty (AppE2 (typeOf xs) (joinConst joinPred') xs zs) ys

--------------------------------------------------------------------------------
-- Push filtering joins into Sort operators

-- | In a join expression, turn references to the input into references to the
-- first tuple component of the input. The first argument provides the new pair
-- type of the input. This rewrite is necessary when pushing filtering joins
-- into the input of a sort operator.
--
-- Note: This is *not* the inverse of 'untuplifyScalarExpr'!
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

joinPushdownR :: RewriteC CL
joinPushdownR =
    readerT $ \cl -> case cl of
        ExprCL AppE2{} -> (pushFilterjoinCompR >>> anytdR pushThroughRewritesR)
                          <+ pushThroughRewritesR
        _              -> fail "can't apply join pushdown rules"
