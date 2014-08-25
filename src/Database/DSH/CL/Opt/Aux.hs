{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf            #-}
{-# LANGUAGE TemplateHaskell       #-}

-- | Common tools for rewrites
module Database.DSH.CL.Opt.Aux
    ( applyExpr
    , applyInjectable
      -- * Monad rewrites with additional state
    , TuplifyM
      -- * Converting predicate expressions into join predicates
    , toJoinExpr
    , splitJoinPredT
    , joinConjunctsT
    , conjunctsT
    -- * Pushing guards towards the front of a qualifier list
    , isThetaJoinPred
    , isSemiJoinPred
    , isAntiJoinPred
      -- * Free and bound variables
    , freeVars
    , compBoundVars
      -- * Substituion
    , substR
    , tuplifyR
      -- * Combining generators and guards
    , insertGuard
      -- * Generic iterator to merge guards into generators
    , Comp(..)
    , MergeGuard
    , mergeGuardsIterR
      -- * Classification of expressions
    , complexPrim1
    , complexPrim2
    , fromGuard
    , fromQual
    , fromGen
      -- * NL spine traversal
    , onetdSpineT
    ) where

import           Control.Arrow
import           Data.Either
import qualified Data.Foldable              as F
import           Data.List
import qualified Data.Set                   as S
import           Data.List.NonEmpty         (NonEmpty ((:|)))
import           Data.Semigroup

import           Language.KURE

import           Database.DSH.CL.Kure
import           Database.DSH.CL.Lang
import           Database.DSH.Common.Lang
import           Database.DSH.Common.RewriteM
import           Database.DSH.Impossible

-- | A version of the CompM monad in which the state contains an additional
-- rewrite. Use case: Returning a tuplify rewrite from a traversal over the
-- qualifier list so that it can be applied to the head expression.
type TuplifyM = RewriteStateM (RewriteC CL)

-- | Run a translate on an expression without context
applyExpr :: TransformC CL b -> Expr -> Either String b
applyExpr f e = runRewriteM $ apply f initialCtx (inject e)

-- | Run a translate on any value which can be injected into CL
applyInjectable :: Injection a CL => TransformC CL b -> a -> Either String b
applyInjectable t e = runRewriteM $ apply t initialCtx (inject e)


--------------------------------------------------------------------------------
-- Rewrite general expressions into equi-join predicates

toJoinBinOp :: Monad m => ScalarBinOp -> m JoinBinOp
toJoinBinOp (SBNumOp o)     = return $ JBNumOp o
toJoinBinOp (SBStringOp o)  = return $ JBStringOp o
toJoinBinOp (SBRelOp _)     = fail "toJoinBinOp: join expressions can't contain relational ops"
toJoinBinOp (SBBoolOp _)    = fail "toJoinBinOp: join expressions can't contain boolean ops"

toJoinUnOp :: Monad m => ScalarUnOp -> m JoinUnOp
toJoinUnOp (SUNumOp o)  = return $ JUNumOp o
toJoinUnOp (SUCastOp o) = return $ JUCastOp o
toJoinUnOp (SUBoolOp _) = fail "toJoinUnOp: join expressions can't contain boolean ops"
toJoinUnOp SUDateOp     = $unimplemented

toJoinExpr :: Ident -> TransformC Expr JoinExpr
toJoinExpr n = do
    e <- idR

    case e of
        AppE1 _ (Prim1 Fst _) _   -> do
            appe1T (toJoinExpr n) (\t _ e1 -> JFst t e1)
        AppE1 _ (Prim1 Snd _) _   -> do
            appe1T (toJoinExpr n) (\t _ e1 -> JSnd t e1)
        BinOp _ o _ _ -> do
            o' <- constT $ toJoinBinOp o
            binopT (toJoinExpr n) (toJoinExpr n) (\t _ e1 e2 -> JBinOp t o' e1 e2)
        UnOp _ o _ -> do
            o' <- constT $ toJoinUnOp o
            unopT (toJoinExpr n) (\t _ e1 -> JUnOp t o' e1)
        Lit t v       -> do
            return $ JLit t v
        Var t x       -> do
            guardMsg (n == x) "toJoinExpr: wrong name"
            return $ JInput t
        _             -> do
            fail "toJoinExpr: can't translate to join expression"

flipRelOp :: BinRelOp -> BinRelOp
flipRelOp Eq  = Eq
flipRelOp NEq = NEq
flipRelOp Gt  = Lt
flipRelOp Lt  = Gt
flipRelOp GtE = LtE
flipRelOp LtE = GtE

-- | Try to transform an expression into a thetajoin predicate. This
-- will fail if either the expression does not have the correct shape
-- (relational operator with simple projection expressions on both
-- sides) or if one side of the predicate has free variables which are
-- not the variables of the qualifiers given to the function.
splitJoinPredT :: Ident -> Ident -> TransformC Expr (JoinConjunct JoinExpr)
splitJoinPredT x y = do
    BinOp _ (SBRelOp op) e1 e2 <- idR

    [x'] <- return $ freeVars e1
    [y'] <- return $ freeVars e2

    if | x == x' && y == y' -> binopT (toJoinExpr x)
                                      (toJoinExpr y)
                                      (\_ _ e1' e2' -> JoinConjunct e1' op e2')
       | y == x' && x == y' -> binopT (toJoinExpr y)
                                      (toJoinExpr x)
                                      (\_ _ e1' e2' -> JoinConjunct e2' (flipRelOp op) e1')
       | otherwise          -> fail "splitJoinPredT: not a theta-join predicate"

-- | Split a conjunctive combination of join predicates.
joinConjunctsT :: Ident -> Ident -> TransformC CL (NonEmpty (JoinConjunct JoinExpr))
joinConjunctsT x y = conjunctsT >>> mapT (splitJoinPredT x y)

-- | Split a combination of logical conjunctions into its sub-terms.
conjunctsT :: TransformC CL (NonEmpty Expr)
conjunctsT = readerT $ \e -> case e of
    -- For a logical AND, turn the left and right arguments into lists
    -- of join predicates and combine them.
    ExprCL (BinOp _ (SBBoolOp Conj) _ _) -> do
        leftConjs  <- childT BinOpArg1 conjunctsT
        rightConjs <- childT BinOpArg2 conjunctsT
        return $ leftConjs <> rightConjs

    -- For a non-AND expression, try to transform it into a join
    -- predicate.
    ExprCL expr -> return $ expr :| []

    _ -> $impossible


--------------------------------------------------------------------------------
-- Distinguish certain kinds of guards

-- | An expression qualifies for a thetajoin predicate if both sides
-- are scalar expressions on exactly one of the join candidate
-- variables.
isThetaJoinPred :: Ident -> Ident -> Expr -> Bool
isThetaJoinPred x y (BinOp _ (SBRelOp _) e1 e2) =
    isFlatExpr e1 && isFlatExpr e1
    && ([x] == freeVars e1 && [y] == freeVars e2
        || [x] == freeVars e2 && [y] == freeVars e1)
isThetaJoinPred _ _ _ = False

-- | Does the predicate look like an existential quantifier?
isSemiJoinPred :: Ident -> Expr -> Bool
isSemiJoinPred x (AppE1 _ (Prim1 Or _)
                           (Comp _ p
                                   (S (BindQ y _)))) = isThetaJoinPred x y p
isSemiJoinPred _  _                                  = False

-- | Does the predicate look like an universal quantifier?
isAntiJoinPred :: Ident -> Expr -> Bool
isAntiJoinPred x (AppE1 _ (Prim1 And _)
                           (Comp _ p
                                   (S (BindQ y _)))) = isThetaJoinPred x y p
isAntiJoinPred _  _                                  = False

isFlatExpr :: Expr -> Bool
isFlatExpr expr =
    case expr of
        AppE1 _ (Prim1 Fst _) e -> isFlatExpr e
        AppE1 _ (Prim1 Snd _) e -> isFlatExpr e
        UnOp _ _ e              -> isFlatExpr e
        BinOp _ _ e1 e2         -> isFlatExpr e1 && isFlatExpr e2
        Var _ _                 -> True
        Lit _ _                 -> True
        _                       -> False

--------------------------------------------------------------------------------
-- Computation of free variables

freeVarsT :: TransformC CL [Ident]
freeVarsT = fmap nub $ crushbuT $ promoteT $ do (ctx, Var _ v) <- exposeT
                                                guardM (v `freeIn` ctx)
                                                return [v]

-- | Compute free variables of the given expression
freeVars :: Expr -> [Ident]
freeVars = either error id . applyExpr freeVarsT

-- | Compute all identifiers bound by a qualifier list
compBoundVars :: F.Foldable f => f Qual -> [Ident]
compBoundVars qs = F.foldr aux [] qs
  where
    aux :: Qual -> [Ident] -> [Ident]
    aux (BindQ n _) ns = n : ns
    aux (GuardQ _) ns  = ns

--------------------------------------------------------------------------------
-- Substitution

alphaLamR :: RewriteC Expr
alphaLamR = do (ctx, Lam lamTy v _) <- exposeT
               v' <- constT $ freshName (inScopeNames ctx)
               let varTy = domainT lamTy
               lamT (extractR $ tryR $ substR v (Var varTy v')) (\_ _ -> Lam lamTy v')

substR :: Ident -> Expr -> RewriteC CL
substR v s = readerT $ \expr -> case expr of
    -- Occurence of the variable to be replaced
    ExprCL (Var _ n) | n == v                          -> return $ inject s

    -- Some other variable
    ExprCL (Var _ _)                                   -> idR

    -- A lambda which does not shadow v and in which v occurs free. If the
    -- lambda variable occurs free in the substitute, we rename the lambda
    -- variable to avoid name capturing.
    ExprCL (Lam _ n e) | n /= v && v `elem` freeVars e ->
        if n `elem` freeVars s
        then promoteR alphaLamR >>> substR v s
        else promoteR $ lamR (extractR $ substR v s)

    -- A lambda which shadows v -> don't descend
    ExprCL (Lam _ _ _)                                 -> idR

    -- If some generator shadows v, we must not substitute in the comprehension
    -- head. However, substitute in the qualifier list. The traversal on
    -- qualifiers takes care of shadowing generators.
    -- FIXME in this case, rename the shadowing generator to avoid
    -- name-capturing (see lambda case)
    ExprCL (Comp _ _ qs) | v `elem` compBoundVars qs   -> promoteR $ compR idR (extractR $ substR v s)
    ExprCL (Comp _ _ _)                                -> promoteR $ compR (extractR $ substR v s) (extractR $ substR v s)

    ExprCL (Lit _ _)                                   -> idR
    ExprCL (Table _ _ _ _)                             -> idR
    ExprCL _                                           -> anyR $ substR v s

    -- Don't substitute past shadowingt generators
    QualsCL ((BindQ n _) :* _) | n == v                -> promoteR $ qualsR (extractR $ substR v s) idR
    QualsCL (_ :* _)                                   -> promoteR $ qualsR (extractR $ substR v s) (extractR $ substR v s)
    QualsCL (S _)                                      -> promoteR $ qualsemptyR (extractR $ substR v s)
    QualCL _                                           -> anyR $ substR v s


--------------------------------------------------------------------------------
-- Tuplifying variables

-- | Turn all occurences of two identifiers into accesses to one tuple variable.
-- tuplifyR z c y e = e[fst z/x][snd z/y]
tuplifyR :: Ident -> (Ident, Type) -> (Ident, Type) -> RewriteC CL
tuplifyR v (v1, t1) (v2, t2) = substR v1 v1Rep >+> substR v2 v2Rep
  where
    (v1Rep, v2Rep) = tupleVars v t1 t2

tupleVars :: Ident -> Type -> Type -> (Expr, Expr)
tupleVars n t1 t2 = (v1Rep, v2Rep)
  where v     = Var pt n
        pt    = pairT t1 t2
        v1Rep = AppE1 t1 (Prim1 Fst (pt .-> t1)) v
        v2Rep = AppE1 t2 (Prim1 Snd (pt .-> t2)) v

--------------------------------------------------------------------------------
-- Helpers for combining generators with guards in a comprehensions'
-- qualifier list

-- | Insert a guard in a qualifier list at the first possible
-- position.
insertGuard :: Expr -> S.Set Ident -> NL Qual -> NL Qual
insertGuard guardExpr initialEnv quals = go initialEnv quals
  where
    go :: S.Set Ident -> NL Qual -> NL Qual
    go env (S q)             =
        if all (\v -> S.member v env) fvs
        then GuardQ guardExpr :* S q
        else q :* (S $ GuardQ guardExpr)
    go env (q@(BindQ x _) :* qs) =
        if all (\v -> S.member v env) fvs
        then GuardQ guardExpr :* q :* qs
        else q :* go (S.insert x env) qs
    go _ (GuardQ _ :* _)      = $impossible

    fvs = freeVars guardExpr

------------------------------------------------------------------------
-- Generic iterator that merges guards into generators one by one.

-- | A container for the components of a comprehension expression
data Comp = C Type Expr (NL Qual)

fromQual :: Qual -> Either (Ident, Expr) Expr
fromQual (BindQ x e) = Left (x, e)
fromQual (GuardQ p)  = Right p


-- | Type of worker functions that merge guards into generators. It
-- receives the comprehension itself (with a qualifier list that
-- consists solely of generators), the current candidate guard
-- expression, guard expressions that have to be tried and guard
-- expressions that have been tried already. Last two are necessary if
-- the merging steps leads to tuplification.
type MergeGuard = Comp -> Expr -> [Expr] -> [Expr] -> TransformC () (Comp, [Expr], [Expr])

tryGuards :: MergeGuard  -- ^ The worker function
          -> Comp        -- ^ The current state of the comprehension
          -> [Expr]      -- ^ Guards to try
          -> [Expr]      -- ^ Guards that have been tried and failed
          -> TransformC () (Comp, [Expr])
-- Try the next guard
tryGuards mergeGuardR comp (p : ps) testedGuards = do
    let tryNextGuard :: TransformC () (Comp, [Expr])
        tryNextGuard = do
            -- Try to combine p with some generators
            (comp', ps', testedGuards') <- mergeGuardR comp p ps testedGuards

            -- On success, back out to give other rewrites
            -- (i.e. predicate pushdown) a chance.
            return (comp', ps' ++ testedGuards')

        -- If the current guard failed, try the next ones.
        tryOtherGuards :: TransformC () (Comp, [Expr])
        tryOtherGuards = tryGuards mergeGuardR comp ps (p : testedGuards)

    tryNextGuard <+ tryOtherGuards

-- No guards left to try and none succeeded
tryGuards _ _ [] _ = fail "no predicate could be merged"

-- | Try to build flat joins (equi-, semi- and antijoins) from a
-- comprehensions qualifier list.
-- FIXME only try on those predicates that look like equi-/anti-/semi-join predicates.
-- FIXME TransformC () ... is an ugly abuse of the rewrite system
mergeGuardsIterR :: MergeGuard -> RewriteC CL
mergeGuardsIterR mergeGuardR = do
    ExprCL (Comp ty e qs) <- idR

    -- Separate generators from guards
    ((g : gs), guards@(_:_)) <- return $ partitionEithers $ map fromQual $ toList qs

    let initialComp = C ty e (fmap (uncurry BindQ) $ fromListSafe g gs)

    -- Try to merge one guard with some generators
    (C _ e' qs', remGuards) <- constT (return ())
                               >>> tryGuards mergeGuardR initialComp guards []

    -- If there are any guards remaining which we could not turn into
    -- joins, append them at the end of the new qualifier list
    case remGuards of
        rg : rgs -> let rqs = fmap GuardQ $ fromListSafe rg rgs
                    in return $ ExprCL $ Comp ty e' (appendNL qs' rqs)
        []       -> return $ ExprCL $ Comp ty e' qs'

--------------------------------------------------------------------------------
-- Traversal functions

-- | Traverse the spine of a NL list top-down and apply the translation as soon
-- as possible.
onetdSpineT
  :: (ReadPath c Int, MonadCatch m, Walker c CL)
  => Transform c m CL b
  -> Transform c m CL b
onetdSpineT t = do
    n <- idR
    case n of
        QualsCL (_ :* _) -> childT 0 t <+ childT 1 (onetdSpineT t)
        QualsCL (S _)    -> childT 0 t
        _                -> $impossible

--------------------------------------------------------------------------------
-- Classification of expressions

complexPrim2 :: Prim2Op -> Bool
complexPrim2 op =
    case op of
        Map       -> False
        ConcatMap -> False
        Pair      -> False
        _         -> True

complexPrim1 :: Prim1Op -> Bool
complexPrim1 op =
    case op of
        Concat -> False
        Fst    -> False
        Snd    -> False
        _      -> True

fromGuard :: Monad m => Qual -> m Expr
fromGuard (GuardQ e)  = return e
fromGuard (BindQ _ _) = fail "not a guard"

fromGen :: Monad m => Qual -> m (Ident, Expr)
fromGen (BindQ x xs) = return (x, xs)
fromGen (GuardQ _)   = fail "not a generator"
