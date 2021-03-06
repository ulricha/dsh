{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | This module implements predicate pushdown on comprehensions.
module Database.DSH.CL.Opt.PredPushdown
  ( predpushdownR
  ) where

import           Control.Arrow
import qualified Data.List.NonEmpty            as N
import qualified Data.Set                      as S

import           Database.DSH.CL.Kure
import           Database.DSH.CL.Lang
import           Database.DSH.CL.Opt.Auxiliary
import qualified Database.DSH.CL.Primitives    as P
import           Database.DSH.Common.Lang
import           Database.DSH.Common.Nat
import           Database.DSH.Common.Kure

{-# ANN module "HLint: ignore Reduce duplication" #-}

--------------------------------------------------------------------------------
-- Auxiliary functions

-- | Return path to occurence of variable x
varPathT :: Ident -> TransformC CL PathC
varPathT x = do
    Var _ x' <- promoteT idR
    guardM $ x == x'
    snocPathToPath <$> absPathT

-- | Collect all paths to variable x in the current expression and
-- turn them into relative paths.
allVarPathsT :: Ident -> TransformC CL [PathC]
allVarPathsT x = do
    varPaths <- collectT $ varPathT x
    guardM $ not $ null varPaths
    parentPathLen <- length . snocPathToPath <$> absPathT
    let localPaths = map (init . drop parentPathLen) varPaths
    return localPaths

--------------------------------------------------------------------------
-- Push a guard into a branch of a join operator

-- | Try to push predicate into the left input of a binary operator
-- which produces tuples: equijoin, nestjoin
pushLeftTupleR :: Ident -> Expr -> RewriteC CL
pushLeftTupleR x p = do
    AppE2 t op xs ys <- promoteT idR

    let predTrans = constT $ return $ inject p

    localPaths <- predTrans >>> allVarPathsT x

    ExprCL p' <- predTrans >>> andR (map (unTuplifyPathR (== TupElem First)) localPaths)

    let xst = typeOf xs

    let filterComp = Comp xst (Var (elemT xst) x) (BindQ x xs :* S (GuardQ p'))
    return $ inject $ AppE2 t op filterComp ys

-- | Try to push predicate into the right input of a binary operator
-- which produces tuples: equijoin
pushRightTupleR :: Ident -> Expr -> RewriteC CL
pushRightTupleR x p = do
    AppE2 t op xs ys <- promoteT idR

    let predTrans = constT $ return $ inject p

    localPaths <- predTrans >>> allVarPathsT x

    ExprCL p' <- predTrans >>> andR (map (unTuplifyPathR (== TupElem (Next First))) localPaths)

    let yst = typeOf ys

    let filterComp = Comp yst (Var (elemT yst) x) (BindQ x ys :* S (GuardQ p'))
    return $ inject $ AppE2 t op xs filterComp

pushLeftOrRightTupleR :: Ident -> Expr -> RewriteC CL
pushLeftOrRightTupleR x p = pushLeftTupleR x p <+ pushRightTupleR x p

-- | Try to push predicates into the left input of a binary operator
-- which produces only the left input, i.e. semijoin, antijoin
pushLeftR :: Ident -> Expr -> RewriteC CL
pushLeftR x p = do
    AppE2 ty op xs ys <- promoteT idR
    let xst = typeOf xs
    let xs' = Comp xst (Var (elemT xst) x) (BindQ x xs :* (S $ GuardQ p))
    return $ inject $ AppE2 ty op xs' ys

--------------------------------------------------------------------------
-- Merging of join predicates into already established theta-join
-- operators
--
-- A predicate can be merged into a theta-join as an additional
-- conjunct if it has the shape of a join predicate and if its left
-- expression refers only to the fst component of the join pair and
-- the right expression refers only to the snd component (or vice
-- versa).

mkMergeableJoinPredT :: Ident -> Expr -> BinRelOp -> Expr -> TransformC CL (JoinConjunct ScalarExpr)
mkMergeableJoinPredT x leftExpr op rightExpr = do
    let constLeftExpr = constT $ return $ inject leftExpr
        constRightExpr = constT $ return $ inject rightExpr

    leftVarPaths  <- constLeftExpr >>> allVarPathsT x
    rightVarPaths <- constRightExpr >>> allVarPathsT x

    leftExpr'     <- constLeftExpr
                         >>> andR (map (unTuplifyPathR (== TupElem First)) leftVarPaths)
                         >>> projectT
                         >>> toScalarExprT x

    rightExpr'    <- constRightExpr
                         >>> andR (map (unTuplifyPathR (== TupElem (Next First))) rightVarPaths)
                         >>> projectT
                         >>> toScalarExprT x

    return $ JoinConjunct leftExpr' op rightExpr'

mirrorRelOp :: BinRelOp -> BinRelOp
mirrorRelOp Eq  = Eq
mirrorRelOp Gt  = Lt
mirrorRelOp GtE = LtE
mirrorRelOp Lt  = Gt
mirrorRelOp LtE = GtE
mirrorRelOp NEq = NEq

splitMergeablePredT :: Ident -> Expr -> TransformC CL (JoinConjunct ScalarExpr)
splitMergeablePredT x p = do
    ExprCL (BinOp _ (SBRelOp op) leftExpr rightExpr) <- return $ inject p
    guardM $ freeVars p == [x]

    -- We might have e1(fst x) op e2(snd x) or e1(snd x) op e2(fst x)
    mkMergeableJoinPredT x leftExpr op rightExpr
      <+ mkMergeableJoinPredT x rightExpr (mirrorRelOp op) leftExpr

-- | If a predicate can be turned into a join predicate, merge it into
-- the current theta join.
mergePredIntoJoinR :: Ident -> Expr -> RewriteC CL
mergePredIntoJoinR x p = do
    AppE2 t (ThetaJoin (JoinPred ps)) xs ys <- promoteT idR
    joinConjunct <- splitMergeablePredT x p

    let extendedJoin = ThetaJoin (JoinPred $ joinConjunct N.<| ps)

    return $ inject $ AppE2 t extendedJoin xs ys

-- | Push into the /first/ argument (input) of some operator that
-- commutes with selection.

-- This was nicer with a higher-order 'sortWith'. With first-order
-- 'sort', we have to push the predicate into both arguments, which
-- works only if the comprehension for the sorting criteria is still
-- in its original form.
pushSortInputR :: Ident -> Expr -> RewriteC CL
pushSortInputR x p = do
    AppE1 t Sort xs <- promoteT idR

    let xst    = typeOf xs
        xt     = elemT xt
        genVar = Var xt x

    p' <- substM x (P.fst genVar) p

    let restrictedInput = Comp xst genVar (BindQ x xs :* S (GuardQ p'))

    return $ inject $ AppE1 t Sort restrictedInput

--------------------------------------------------------------------------
-- Take remaining comprehension guards and try to push them into the
-- generator. This might be accomplished by either merging it into a
-- join, pushing it into a join input or pushing it through some other
-- operator that commutes with selection (e.g. sorting).

pushPredicateR :: Ident -> Expr -> RewriteC CL
pushPredicateR x p =
    readerT $ \e -> case e of
        -- First, try to merge the predicate into the join. For
        -- regular joins and products, non-join predicates might apply
        -- to the left or right input.
        ExprCL (AppE2 _ (ThetaJoin _) _ _) -> mergePredIntoJoinR x p
                                              <+ pushLeftOrRightTupleR x p
        ExprCL (AppE2 _ CartProduct _ _)   -> pushLeftOrRightTupleR x p

        -- For nesting operators, a guard can only refer to the left
        -- input, i.e. the original outer generator.

        ExprCL NestJoinP{}                 -> pushLeftTupleR x p
        ExprCL GroupJoinP{}                -> pushLeftTupleR x p

        -- Semi- and Antijoin operators produce a subset of their left
        -- input. A filter can only apply to the left input,
        -- consequently.
        ExprCL (AppE2 _ (SemiJoin _) _ _)  -> pushLeftR x p
        ExprCL (AppE2 _ (AntiJoin _) _ _)  -> pushLeftR x p

        -- Sorting commutes with selection
        ExprCL (AppE1 _ Sort _)            -> pushSortInputR x p
        _                                  -> fail "expression does not allow predicate pushing"

pushQualsR :: RewriteC CL
pushQualsR = do
    BindQ x _ :* GuardQ p :* qs <- promoteT idR
    [x'] <- return $ freeVars p
    guardM $ x == x'
    ExprCL gen' <- pathT [QualsHead, BindQualExpr] (pushPredicateR x p)
    return $ inject $ BindQ x gen' :* qs

pushQualsEndR :: RewriteC CL
pushQualsEndR = do
    BindQ x _ :* S (GuardQ p) <- promoteT idR
    [x'] <- return $ freeVars p
    guardM $ x == x'
    ExprCL gen' <- pathT [QualsHead, BindQualExpr] (pushPredicateR x p)
    return $ inject $ S $ BindQ x gen'

pushDownSinglePredR :: RewriteC CL
pushDownSinglePredR = do
    Comp{} <- promoteT idR
    childR CompQuals (promoteR $ pushQualsR <+ pushQualsEndR)

pushDownPredsR :: MergeGuard
pushDownPredsR comp guard guardsToTry leftOverGuards = do
    let C ty h qs = comp
    env <- S.fromList . inScopeNames <$> contextT
    let compExpr = ExprCL $ Comp ty h (insertGuard guard env qs)
    ExprCL (Comp _ _ qs') <- constT (return compExpr) >>> pushDownSinglePredR
    return (C ty h qs', guardsToTry, leftOverGuards)

-- | Push down all guards in a qualifier list, if possible.
predpushdownR :: RewriteC CL
predpushdownR = logR "predpushdown" $ mergeGuardsIterR pushDownPredsR
