{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf            #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE TemplateHaskell       #-}

-- | Common tools for rewrites
module Database.DSH.CL.Opt.Auxiliary
    ( applyExpr
    , applyInjectable
      -- * Monad rewrites with additional state
    , TuplifyM
      -- * Convert join predicates into general expressions
    , fromScalarExpr
      -- * Converting predicate expressions into join predicates
    , toScalarExpr
    , splitJoinPredT
    , joinConjunctsT
    , conjunctsT
      -- * Helpers on scalar expressions
    , firstOnly
    , untuplifyScalarExpr
      -- * Pushing guards towards the front of a qualifier list
    , isThetaJoinPred
    , isSemiJoinPred
    , isAntiJoinPred
    , isFlatExpr
      -- * Free and bound variables
    , freeVars
    , boundVars
    , compBoundVars
      -- * Substituion
    , substR
    , tuplifyR
    , unTuplifyR
    , unTuplifyPathR
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
    , isFilteringJoin
      -- * NL spine traversal
    , onetdSpineT
      -- * Path utilities
    , localizePathT
      -- * Pattern synonyms for expressions
    , pattern ConcatP
    , pattern SingletonP
    , pattern GuardP
    , pattern SemiJoinP
    , pattern NestJoinP
    , pattern GroupJoinP
    , pattern NestProductP
    , pattern AndP
    , pattern OrP
    , pattern SortP
    , pattern NotP
    , pattern EqP
    , pattern LengthP
    , pattern NullP
    , pattern FalseP
    , pattern TrueP
    , pattern TupFirstP
    , pattern TupSecondP
    , pattern (:<-:)
    , pattern LitListP
    , pattern SingleJoinPredP
    ) where

import           Control.Arrow
import           Data.Either
import qualified Data.Foldable                  as F
import           Data.List
import           Data.List.NonEmpty             (NonEmpty ((:|)))
import           Data.Semigroup                 hiding (First)
import qualified Data.Set                       as S

import           Language.KURE

import           Database.DSH.CL.Kure
import           Database.DSH.CL.Lang
import           Database.DSH.Common.Impossible
import           Database.DSH.Common.Lang
import           Database.DSH.Common.Nat
import           Database.DSH.Common.RewriteM

-- | A version of the CompM monad in which the state contains an additional
-- rewrite. Use case: Returning a tuplify rewrite from a traversal over the
-- qualifier list so that it can be applied to the head expression.
type TuplifyM = RewriteStateM (RewriteC CL) LogC

-- | Run a translate on an expression without context
applyExpr :: TransformC CL b -> Expr -> Either String b
applyExpr f e = fst <$> runRewriteM (applyT f initialCtx (inject e))

-- | Run a translate on any value which can be injected into CL
applyInjectable :: Injection a CL => TransformC CL b -> a -> Either String b
applyInjectable t e = fst <$> runRewriteM (applyT t initialCtx (inject e))

--------------------------------------------------------------------------------
-- Rewrite join predicates into general expressions.

-- | 'fromScalarExpr n e' rewrites scalar expression 'e' into a general
-- expression and uses the name 'n' for the input variable.
fromScalarExpr :: MonadCatch m => Ident -> ScalarExpr -> m Expr
fromScalarExpr n e@(JBinOp op e1 e2)    = BinOp (typeOf e) op
                                              <$> fromScalarExpr n e1
                                              <*> fromScalarExpr n e2
fromScalarExpr n e@(JUnOp op e1)        = UnOp (typeOf e) op
                                              <$> fromScalarExpr n e1
fromScalarExpr n e@(JTupElem tupIdx e1) = AppE1 (typeOf e) (TupElem tupIdx)
                                              <$> fromScalarExpr n e1
fromScalarExpr _ (JLit ty val)          = pure $ Lit ty val
fromScalarExpr n (JInput ty)            = pure $ Var ty n

--------------------------------------------------------------------------------
-- Rewrite general expressions into equi-join predicates

toScalarExpr :: Ident -> TransformC Expr ScalarExpr
toScalarExpr n = do
    e <- idR

    case e of
        AppE1 _ (TupElem i) _ ->
            appe1T (toScalarExpr n) (\_ _ e1 -> JTupElem i e1)
        BinOp _ o _ _ ->
            binopT (toScalarExpr n) (toScalarExpr n) (\_ _ e1 e2 -> JBinOp o e1 e2)
        UnOp _ o _ ->
            unopT (toScalarExpr n) (\_ _ e1 -> JUnOp o e1)
        Lit t v       ->
            return $ JLit t v
        Var t x       -> do
            guardMsg (n == x) "toScalarExpr: wrong name"
            return $ JInput t
        _             ->
            fail "toScalarExpr: can't translate to join expression"

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
splitJoinPredT :: Ident -> Ident -> TransformC Expr (JoinConjunct ScalarExpr)
splitJoinPredT x y = do
    BinOp _ (SBRelOp op) e1 e2 <- idR

    [x'] <- return $ freeVars e1
    [y'] <- return $ freeVars e2

    if | x == x' && y == y' -> binopT (toScalarExpr x)
                                      (toScalarExpr y)
                                      (\_ _ e1' e2' -> JoinConjunct e1' op e2')
       | y == x' && x == y' -> binopT (toScalarExpr y)
                                      (toScalarExpr x)
                                      (\_ _ e1' e2' -> JoinConjunct e2' (flipRelOp op) e1')
       | otherwise          -> fail "splitJoinPredT: not a theta-join predicate"

-- | Split a conjunctive combination of join predicates.
joinConjunctsT :: Ident -> Ident -> TransformC CL (NonEmpty (JoinConjunct ScalarExpr))
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
-- Helpers on scalar expressions

-- | Check whether a scalar expression refers only to the first tuple component
-- of the input.
firstOnly :: ScalarExpr -> Bool
firstOnly (JBinOp _ e1 e2)          = firstOnly e1 && firstOnly e2
firstOnly (JUnOp _ e)               = firstOnly e
firstOnly (JTupElem First JInput{}) = True
firstOnly (JTupElem _     JInput{}) = False
firstOnly (JTupElem _     e)        = firstOnly e
firstOnly JLit{}                    = True
firstOnly JInput{}                  = $impossible

-- | Change a scalar expression that only refers to the first tuple component of
-- the input to refer directly to the input.
untuplifyScalarExpr :: ScalarExpr -> ScalarExpr
untuplifyScalarExpr (JBinOp op e1 e2)                          = JBinOp op (untuplifyScalarExpr e1) (untuplifyScalarExpr e2)
untuplifyScalarExpr (JUnOp op e)                               = JUnOp op (untuplifyScalarExpr e)
untuplifyScalarExpr (JTupElem First (JInput (TupleT [t1, _]))) = JInput t1
untuplifyScalarExpr (JTupElem _ (JInput _))                    = $impossible
untuplifyScalarExpr (JTupElem idx e)                           = JTupElem idx (untuplifyScalarExpr e)
untuplifyScalarExpr (JLit ty val)                              = JLit ty val
untuplifyScalarExpr (JInput _)                                 = $impossible

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
isSemiJoinPred x (OrP (Comp _ p (S (BindQ y _)))) = isThetaJoinPred x y p
isSemiJoinPred _  _                               = False

-- | Does the predicate look like an universal quantifier?
isAntiJoinPred :: Ident -> Expr -> Bool
isAntiJoinPred x (AndP (Comp _ p (S (BindQ y _)))) = isThetaJoinPred x y p
isAntiJoinPred _  _                                = False

isFlatExpr :: Expr -> Bool
isFlatExpr expr =
    case expr of
        AppE1 _ (TupElem _) e -> isFlatExpr e
        UnOp _ _ e            -> isFlatExpr e
        BinOp _ _ e1 e2       -> isFlatExpr e1 && isFlatExpr e2
        Var _ _               -> True
        Lit _ _               -> True
        _                     -> False

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
compBoundVars = F.foldr aux []
  where
    aux :: Qual -> [Ident] -> [Ident]
    aux (BindQ n _) ns = n : ns
    aux (GuardQ _) ns  = ns

boundVarsT :: TransformC CL [Ident]
boundVarsT = fmap nub $ crushbuT $ promoteT $ readerT $ \expr -> case expr of
     Comp _ _ qs -> return $ compBoundVars qs
     Let _ v _ _ -> return [v]
     _           -> return []

-- | Compute all names that are bound in the given expression. Note
-- that the only binding forms in NKL are comprehensions or 'let'
-- bindings.
boundVars :: Expr -> [Ident]
boundVars = either error id . applyExpr boundVarsT

--------------------------------------------------------------------------------
-- Substitution

-- | /Exhaustively/ substitute term 's' for a variable 'v'.
substR :: Ident -> Expr -> RewriteC CL
substR v s = readerT $ \expr -> case expr of
    -- Occurence of the variable to be replaced
    ExprCL (Var _ n) | n == v                          -> return $ inject s

    -- If a let-binding shadows the name we substitute, only descend
    -- into the bound expression.
    ExprCL (Let _ n _ _)
        | n == v    -> tryR $ childR LetBind (substR v s)
        | otherwise -> if n `elem` freeVars s
                       -- If the let-bound name occurs free in the substitute,
                       -- alpha-convert the binding to avoid capturing the name.
                       then $unimplemented >>> tryR (anyR (substR v s))
                       else tryR $ anyR (substR v s)

    -- If some generator shadows v, we must not substitute in the comprehension
    -- head. However, substitute in the qualifier list. The traversal on
    -- qualifiers takes care of shadowing generators.
    -- FIXME in this case, rename the shadowing generator to avoid
    -- name-capturing (see lambda case)
    ExprCL (Comp _ _ qs) | v `elem` compBoundVars qs   -> tryR $ childR CompQuals (substR v s)
    ExprCL _                                           -> tryR $ anyR $ substR v s

    -- Don't substitute past shadowing generators
    QualsCL (BindQ n _ :* _) | n == v                  -> tryR $ childR QualsHead (substR v s)
    QualsCL _                                          -> tryR $ anyR $ substR v s
    QualCL _                                           -> tryR $ anyR $ substR v s


--------------------------------------------------------------------------------
-- Tuplifying and Untuplifying variables

-- | Turn all occurences of two identifiers into accesses to one tuple variable.
-- tuplifyR z c y e = e[fst z/x][snd z/y]
tuplifyR :: Ident -> (Ident, Type) -> (Ident, Type) -> RewriteC CL
tuplifyR v (v1, t1) (v2, t2) = substR v1 v1Rep >+> substR v2 v2Rep
  where
    (v1Rep, v2Rep) = tupleVars v t1 t2

tupleVars :: Ident -> Type -> Type -> (Expr, Expr)
tupleVars n t1 t2 = (v1Rep, v2Rep)
  where v     = Var pt n
        pt    = PPairT t1 t2
        v1Rep = AppE1 t1 (TupElem First) v
        v2Rep = AppE1 t2 (TupElem (Next First)) v

-- | Remove tuple accessor from a variable.
unTuplifyR :: (Prim1 -> Bool) -> RewriteC CL
unTuplifyR isTupleOp = do
    AppE1 ty op (Var _ x)  <- promoteT idR
    guardM $ isTupleOp op
    return $ inject $ Var ty x

-- | Remove tuple accessor from a variable at a specific path.
unTuplifyPathR :: (Prim1 -> Bool) -> PathC -> RewriteC CL
unTuplifyPathR isTupleOp path = pathR path (unTuplifyR isTupleOp)

--------------------------------------------------------------------------------
-- Helpers for combining generators with guards in a comprehensions'
-- qualifier list

-- | Insert a guard in a qualifier list at the first possible position.
-- 'insertGuard' expects the guard expression to insert, the initial name
-- envionment above the qualifiers and the list of qualifiers.
insertGuard :: Expr -> S.Set Ident -> NL Qual -> NL Qual
insertGuard guardExpr = go
  where
    go :: S.Set Ident -> NL Qual -> NL Qual
    go env (S q)                 =
        if all (`S.member` env) fvs
        then GuardQ guardExpr :* S q
        else q :* (S $ GuardQ guardExpr)
    go env (q@(BindQ x _) :* qs) =
        if all (`S.member` env) fvs
        then GuardQ guardExpr :* q :* qs
        else q :* go (S.insert x env) qs
    go env (GuardQ p :* qs)      =
        if all (`S.member` env) fvs
        then GuardQ guardExpr :* GuardQ p :* qs
        else GuardQ p :* go env qs

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
    (g : gs, guards@(_:_)) <- return $ partitionEithers $ map fromQual $ toList qs

    let initialComp = C ty e (uncurry BindQ <$> fromListSafe g gs)

    -- Try to merge one guard with some generators
    (C _ e' qs', remGuards) <- constT (return ())
                               >>> tryGuards mergeGuardR initialComp guards []

    -- If there are any guards remaining which we could not turn into
    -- joins, append them at the end of the new qualifier list
    case remGuards of
        rg : rgs -> let rqs = GuardQ <$> fromListSafe rg rgs
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

complexPrim2 :: Prim2 -> Bool
complexPrim2 _ = True

complexPrim1 :: Prim1 -> Bool
complexPrim1 op =
    case op of
        Concat    -> False
        TupElem _ -> False
        _         -> True

fromGuard :: Monad m => Qual -> m Expr
fromGuard (GuardQ e)  = return e
fromGuard (BindQ _ _) = fail "not a guard"

fromGen :: Monad m => Qual -> m (Ident, Expr)
fromGen (BindQ x xs) = return (x, xs)
fromGen (GuardQ _)   = fail "not a generator"

-- | Filtering joins are joins that only remove tuples from their left input
-- (i.e. SemiJoin, AntiJoin).
isFilteringJoin :: Monad m => Prim2 -> m (JoinPredicate ScalarExpr -> Prim2, JoinPredicate ScalarExpr)
isFilteringJoin joinOp =
    case joinOp of
        SemiJoin p -> return (SemiJoin, p)
        AntiJoin p -> return (AntiJoin, p)
        _          -> fail "not a pushable join operator"


--------------------------------------------------------------------------------
-- Path utilities

-- | Turn an absolute path into a local path.
localizePathT :: PathC -> TransformC CL (Path CrumbC)
localizePathT path = do
    pathLen <- length . snocPathToPath <$> absPathT
    return $ drop pathLen path

--------------------------------------------------------------------------------
-- Pattern synonyms for expressions

pattern ConcatP xs           <- AppE1 _ Concat xs
pattern SingletonP x         <- AppE1 _ Singleton x
pattern GuardP p             <- AppE1 _ Guard p
pattern SemiJoinP ty p xs ys = AppE2 ty (SemiJoin p) xs ys
pattern NestJoinP ty p xs ys = AppE2 ty (NestJoin p) xs ys
pattern GroupJoinP ty p as xs ys = AppE2 ty (GroupJoin p as) xs ys
pattern NestProductP ty xs ys = AppE2 ty NestProduct xs ys
pattern AndP xs              <- AppE1 _ (Agg And) xs
pattern OrP xs              <- AppE1 _ (Agg Or) xs
pattern SortP ty xs          = AppE1 ty Sort xs
pattern NotP e               <- UnOp _ (SUBoolOp Not) e
pattern EqP e1 e2 <- BinOp _ (SBRelOp Eq) e1 e2
pattern LengthP e <- AppE1 _ (Agg Length) e
pattern NullP e <- AppE1 _ Null e
pattern TrueP = Lit PBoolT (ScalarV (BoolV True))
pattern FalseP = Lit PBoolT (ScalarV (BoolV False))
pattern TupFirstP t e = AppE1 t (TupElem First) e
pattern TupSecondP t e = AppE1 t (TupElem (Next First)) e
pattern a :<-: b = BindQ a b
pattern LitListP ty vs = Lit ty (ListV vs)
pattern SingleJoinPredP r o l <- JoinPred (JoinConjunct r o l :| [])
