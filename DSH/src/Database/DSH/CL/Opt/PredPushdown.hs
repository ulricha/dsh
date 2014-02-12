{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE LambdaCase          #-}
    
-- | This module implements predicate pushdown on comprehensions.
module Database.DSH.CL.Opt.PredPushdown
  ( predpushdownR
  ) where
  
import Debug.Trace

import           Control.Applicative
import           Control.Arrow
import qualified Data.Set as S
import qualified Data.Map as M

import Database.DSH.Impossible

import           Database.DSH.Common.Pretty
import           Database.DSH.CL.Lang
import           Database.DSH.CL.Kure
import           Database.DSH.CL.Opt.Aux

--------------------------------------------------------------------------------
-- Push a comprehension guard through a join operator

-- | Return path to occurence of variable x
varPathT :: Ident -> TranslateC CL PathC
varPathT x = do
    Var _ x' <- promoteT idR
    guardM $ x == x'
    snocPathToPath <$> absPathT

-- | Collect all paths to variable x in the current expression and
-- turn them into relative paths.
allVarPathsT :: Ident -> TranslateC CL [PathC]
allVarPathsT x = do
    varPaths <- collectT $ varPathT x
    guardM $ not $ null varPaths
    parentPathLen <- length <$> snocPathToPath <$> absPathT
    let localPaths = map (init . drop parentPathLen) varPaths
    return localPaths

-- | All occurences of variable x must occur in the form of a tuple
-- accessor, either fst or snd. Remove this tuple accessor.
unTuplifyR :: (Prim1Op -> Bool) -> PathC -> RewriteC CL
unTuplifyR isTupleOp path = pathR path $ do
    AppE1 ty (Prim1 op _) (Var _ x)  <- promoteT idR
    guardM $ isTupleOp op
    return $ inject $ Var ty x

-- | Try to push predicate into the left input of a binary operator
-- which produces tuples: equijoin, nestjoin, nestproduct
pushLeftTupleR :: Ident -> Expr -> RewriteC CL
pushLeftTupleR x p = do
    AppE2 t op xs ys <- promoteT idR

    let predTrans = constT $ return $ inject p

    localPaths <- predTrans >>> allVarPathsT x

    ExprCL p' <- predTrans >>> andR (map (unTuplifyR (== Fst)) localPaths)

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

    ExprCL p' <- predTrans >>> andR (map (unTuplifyR (== Snd)) localPaths)

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

pushPredicateR :: Ident -> Expr -> RewriteC CL
pushPredicateR x p = do
    readerT $ \case
        -- For regular joins and products, predicates might apply to
        -- the left or right input.
        ExprCL (AppE2 _ (Prim2 (EquiJoin _ _) _) _ _) -> pushLeftOrRightTupleR x p
        ExprCL (AppE2 _ (Prim2 CartProduct _) _ _)    -> pushLeftOrRightTupleR x p
    
        -- For nesting operators, a guard can only refer to the left
        -- input, i.e. the original outer generator.

        -- ExprCL (AppE2 _ (Prim2 (NestProduct _ _) _) _ _) -> pushLeftTupleR p
        ExprCL (AppE2 _ (Prim2 (NestJoin _ _) _) _ _)    -> pushLeftTupleR x p

        -- Semi- and Antijoin operators produce a subset of their left
        -- input. A filter can only apply to the left input,
        -- consequently.
        ExprCL (AppE2 _ (Prim2 (SemiJoin _ _) _) _ _) -> pushLeftR x p
        ExprCL (AppE2 _ (Prim2 (AntiJoin _ _) _) _ _) -> pushLeftR x p
        _                                             -> fail "expression does not allow predicate pushing"

pushQualsR :: RewriteC CL
pushQualsR = do
    BindQ x _ :* GuardQ p :* qs <- promoteT idR
    [x'] <- return $ freeVars p
    guardM $ x == x'
    ExprCL gen' <- pathT [QualsHead, BindQualExpr] (pushPredicateR x p)
    return $ inject $ BindQ x gen' :* qs

pushQualsEndR :: RewriteC CL
pushQualsEndR = do
    BindQ x _ :* (S (GuardQ p)) <- promoteT idR
    [x'] <- return $ freeVars p
    guardM $ x == x'
    ExprCL gen' <- pathT [QualsHead, BindQualExpr] (pushPredicateR x p)
    return $ inject $ S $ BindQ x gen'

pushDownSinglePredR :: RewriteC CL
pushDownSinglePredR = do
    Comp _ _ _ <- promoteT idR
    childR CompQuals (promoteR $ pushQualsR <+ pushQualsEndR)

pushDownPredsR :: MergeGuard
pushDownPredsR comp guard guardsToTry leftOverGuards = do
    let C ty h qs = comp
    env <- S.fromList <$> inScopeNames <$> contextT
    let compExpr = ExprCL $ Comp ty h (insertGuard guard env qs)
    ExprCL (Comp _ _ qs') <- constT (return compExpr) >>> pushDownSinglePredR
    return (C ty h qs', guardsToTry, leftOverGuards)

-- | Push down all guards in a qualifier list, if possible.
predpushdownR :: RewriteC CL
predpushdownR = mergeGuardsIterR pushDownPredsR
