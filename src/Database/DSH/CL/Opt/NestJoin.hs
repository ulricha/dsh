{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}

-- | Deal with nested comprehensions by introducing explicit nesting
-- operators (NestJoin).
module Database.DSH.CL.Opt.NestJoin
  ( nestjoinR
  , zipCorrelatedR
  ) where

import           Control.Arrow
import           Control.Monad
import           Data.Either

import           Data.List
import           Data.List.NonEmpty                    (NonEmpty ((:|)))
import qualified Data.Map                              as M
import qualified Data.Set                              as S

import           Database.DSH.Common.Kure
import           Database.DSH.Common.Lang

import           Database.DSH.CL.Kure
import           Database.DSH.CL.Lang

import qualified Database.DSH.CL.Primitives            as P

import           Database.DSH.CL.Opt.Auxiliary
import           Database.DSH.CL.Opt.CompNormalization

nestjoinR :: RewriteC CL
nestjoinR =    logR "nestjoin.guard" unnestQualsR'
            <+ logR "nestjoin.head" unnestHeadR

--------------------------------------------------------------------------------
-- Common code for unnesting from a comprehension head and from
-- comprehension guards

--------------------------------------------------------------------------------
-- Nestjoin introduction: unnesting comprehensions from complex predicates


--------------------------------------------------------------------------------
-- Rules that bring nested comprehension patterns into forms that are
-- suitable for unnesting

-- | De-Normalization: This rule is the inverse of rule M-Norm-3
-- [ [ f y | y <- g x ] x <- xs ]
-- =>
-- [ [ f z | z <- y ] | y <- [ g x | x <- xs ] ]
-- provided that
-- (a) g is complex/expensive
-- (b) g contains a comprehension
--
-- The original comprehension produces a collection for every rule of
-- the outer collection xs and then directly performs an action on all
-- elements of the inner collections. The problem here is that the
-- comprehension nested in g might be combined into a nesting operator
-- with xs (maybe even a nestjoin), but the enclosing comprehension
-- blocks this.

--------------------------------------------------------------------------------
-- Other forms of unnesting

isComplexExpr :: Expr -> Bool
isComplexExpr e =
    case e of
        Comp{}         -> True
        If{}           -> True
        BinOp{}        -> True
        UnOp{}         -> True
        AppE2 _ op _ _ -> complexPrim2 op
        AppE1 _ op _   -> complexPrim1 op
        Lit{}          -> False
        Var{}          -> False
        Table{}        -> False
        MkTuple{}      -> False
        Let{}          -> False

containsComplexExprT :: TransformC CL ()
containsComplexExprT = onetdT isComplexExprT
  where
    isComplexExprT :: TransformC CL ()
    isComplexExprT = do
        e <- promoteT idR
        guardM $ isComplexExpr e
        return ()

-- | If a inner comprehension iterates over a complex function of the
-- outer element, pull the function out. The motivation of this
-- rewrite is the following: f is work performed in the head for every
-- x. The rewrite does not change that (f actually has to be performed
-- for every x), but it moves the work out of the head. This might
-- enable subsequent rewrites to move f out of the head of other
-- enclosing comprehensions as well (model use case: dft).
--
-- [ [ e x y | y <- f x ] | x <- xs ]
-- => [ [ f [x/fst z] y | y <- snd z ] | z <- zip xs [ f x | x <- xs ] ]
--
-- provided that f is "complex".
--
-- We need the zip to provide the correlation between one x and the
-- group produced by f for this particular x.
--
-- Note: This rule is actually a special case of the inverse M-Norm-3
-- rule provided above.
zipCorrelatedR :: RewriteC CL
zipCorrelatedR = logR "nestjoin.zipcorrelated" $ do
    Comp to (Comp ti e (S (BindQ y f))) (S (BindQ x xs)) <- promoteT idR

    let fvs = freeVars e
    guardM $ x `elem` fvs && y `elem` fvs

    guardM $ x `elem` freeVars f

    -- Is f complex as required?
    void $ pathT [CompHead, CompQuals, QualsSingleton, BindQualExpr] containsComplexExprT

    z <- freshNameT [y]

    let genComp = Comp (ListT $ typeOf f) f (S $ BindQ x xs)
        zipGen  = P.zip xs genComp
        zt      = elemT $ typeOf zipGen
        zv      = Var zt z

    f' <- substM x (P.fst zv) e

    let innerComp = Comp ti f' (S $ BindQ y (P.snd zv))
        outerComp = Comp to innerComp (S (BindQ z zipGen))

    return $ inject outerComp

--------------------------------------------------------------------------------
-- Normalization of nesting patterns

-- | Consider the case in which a comprehension is hidden in the
-- generator of an inner comprehension, such that the generator
-- depends on the outer variable and the inner comprehension can not
-- be unnested.
--
-- In this case, perform the inverse rewrite to M-Norm-3: Nest the
-- generator expression into the outer comprehension
--
-- [ [ e y | y <- g x ] | x <- xs ]
-- =>
-- [ [ e y | y <- z ] | z <- [ g x | x <- xs ] ]
--
-- provided that g contains at least one unnestable comprehension
--
-- Important: This is the dual rewrite to M-Norm-3. An unconditional
-- application will lead into a rewriting loop. It **must** be
-- combined with a rewrite that makes progress on g and xs.
-- nestingGenR :: RewriteC CL
-- nestingGenR = logR "nestjoin.nestinggen" $ do
--     Comp  to (Comp ti e (S (BindQ y g))) (S (BindQ x xs)) <- promoteT idR

--     -- Generator expression g should depend on x (otherwise we could
--     -- unnest directly
--     guardM $ x `elem` freeVars g

--     -- Generator expression g should contain at least one unnestable
--     -- comprehension
--     void $ constNodeT g >>> searchNestedCompT x

--     z <- freshNameT []

--     let gty = typeOf g

--     let innerComp = Comp ti e (S (BindQ y (Var gty z)))
--         genComp   = Comp (ListT gty) g (S (BindQ x xs))
--         outerComp = Comp to innerComp (S (BindQ z genComp))

--     return $ inject outerComp

--------------------------------------------------------------------------------
-- Normalization of nesting patterns

type NestM = RewriteStateM (Maybe ((Ident, Expr), JoinPredicate ScalarExpr, (Ident, [Expr]))) RewriteLog

-- | Check if a nested comprehension matches the current candidate generator.
-- Rewrite the nested comprehension into a comprehension over the inner nestjoin
-- result and return all information necessary to construct the nestjoin
-- operator.
unnestCompR :: S.Set Ident -> (Ident, Type) -> Rewrite CompCtx NestM CL
unnestCompR locallyBoundVars (x, xTy) = do
    Comp t h (BindQ y ys :* qs) <- promoteT idR
    let yfvs = freeVarsS ys
    guardM $ S.null $ locallyBoundVars `S.intersection` yfvs
    guardM $ not $ S.member x yfvs

    guardExps <- constT $ mapM fromGuard qs
    let (nonJoinPreds, joinConjs) = partitionEithers $ map (splitJoinPredE x y) $ toList guardExps

    c : cs <- pure joinConjs
    let joinPred = JoinPred $ c :| cs

    -- Identify predicates which only refer to y and can be evaluated
    -- on the right nestjoin input.
    let (yPreds, leftOverPreds) = partition ((== [y]) . freeVars) nonJoinPreds

    scopeNames <- S.fromList <$> inScopeNames <$> contextT
    innerName   <- liftstateT $ freshNameT [y]
    outerName   <- liftstateT $ freshNameT [y]

    let ysTy           = typeOf ys
        yTy            = elemT ysTy
        h'             = tuplifyE scopeNames innerName (x, xTy) (y, yTy) h
        leftOverPreds' = map (tuplifyE scopeNames innerName (x, xTy) (y, yTy)) leftOverPreds
        leftOverGuards = map GuardQ leftOverPreds'
        joinVar        = Var (PPairT xTy (ListT $ PPairT xTy yTy)) outerName

    constT $ put $ Just ((outerName, ys), joinPred, (y, yPreds))

    case leftOverGuards of
        g : gs -> pure $ inject $ Comp t h' (BindQ innerName (P.snd joinVar) :* fromListSafe g gs)
        []     -> pure $ inject $ Comp t h' (S $ BindQ innerName (P.snd joinVar))

-- | Traverse an expression searching for nestjoin opportunities for the current
-- candidate generator.
searchHeadR :: S.Set Ident -> (Ident, Type) -> Rewrite CompCtx NestM CL
searchHeadR locallyBoundVars (x, xTy) = readerT $ \cl -> case cl of
    ExprCL (Let _ x' _ _)
        | x == x'   -> fail "shadowing"
        | otherwise -> childR LetBind (searchHeadR locallyBoundVars (x, xTy))
                       <+ childR LetBody (searchHeadR (S.insert x' locallyBoundVars) (x, xTy))
    ExprCL Comp{} -> tryR (liftstateT guardpushbackR) >>> unnestCompR locallyBoundVars (x, xTy)
                         <+ childT CompQuals (searchQualsR locallyBoundVars (x, xTy))
    ExprCL _ -> oneR $ searchHeadR locallyBoundVars (x, xTy)
    _ -> fail "only expressions"

searchQualsR :: S.Set Ident -> (Ident, Type) -> Rewrite CompCtx NestM CL
searchQualsR locallyBoundVars (x, xTy) = readerT $ \cl -> case cl of
    QualsCL (BindQ x' _ :* _)
        | x == x'   ->
            pathR [QualsHead, BindQualExpr] (searchHeadR locallyBoundVars (x, xTy))
        | otherwise ->
            pathR [QualsHead, BindQualExpr] (searchHeadR locallyBoundVars (x, xTy))
            <+
            childR QualsHead (searchQualsR (S.insert x' locallyBoundVars) (x, xTy))
    QualsCL (S BindQ{}) ->
        pathR [QualsSingleton, BindQualExpr] (searchHeadR locallyBoundVars (x, xTy))
    QualsCL (GuardQ _ :* _) ->
            pathR [QualsHead, GuardQualExpr] (searchHeadR locallyBoundVars (x, xTy))
            <+
            childR QualsTail (searchQualsR locallyBoundVars (x, xTy))
    QualsCL (S (GuardQ _)) ->
        pathR [QualsSingleton, GuardQualExpr] (searchHeadR locallyBoundVars (x, xTy))
    _ -> fail "not a qualifier"

-- | Traverse qualifiers from the current candidate generator to the end. Once
-- reaching the end, traverse the head searching for a nestjoin opportunity that
-- matches the candidate generator. Collect names bound between the candidate
-- generator and the head.
traverseToHeadT :: S.Set Ident -> (Ident, Type) -> Expr -> Transform CompCtx NestM CL Expr
traverseToHeadT locallyBoundVars (x, xTy) h = readerT $ \qs -> case qs of
    QualsCL (BindQ x' _ :* _)
        | x == x'   -> fail "shadowing"
        | otherwise -> childT QualsTail $ traverseToHeadT (S.insert x' locallyBoundVars) (x, xTy) h
    QualsCL (GuardQ _ :* _) -> childT QualsTail $ traverseToHeadT locallyBoundVars (x, xTy) h
    QualsCL (S (BindQ x' _))
        | x == x'   -> fail "shadowing"
        | otherwise -> do
          constT (pure $ inject h) >>> searchHeadR (S.insert x' locallyBoundVars) (x, xTy) >>> projectT
    QualsCL (S (GuardQ _)) -> do
        constT (pure $ inject h) >>> searchHeadR locallyBoundVars (x, xTy) >>> projectT
    _ -> fail "no qualifiers"

-- | Execute a transformation with a given context.
withContextT :: c -> Transform c m a b -> Transform c m a b
withContextT c t = liftContext (const c) t

-- | The element type of a nest join result, given the element types of the
-- inputs.
nestJoinElemTy :: Type -> Type -> Type
nestJoinElemTy xTy yTy = PPairT xTy (ListT $ PPairT xTy yTy)

-- | Construct a nestjoin operator from both join operands, a join predicate and
-- additional predicates for the right input.
mkJoin :: Expr -> Expr -> JoinPredicate ScalarExpr -> (Ident, [Expr]) -> Expr
mkJoin xs ys joinPred (y, yPreds) =
    AppE2 (ListT $ nestJoinElemTy xTy yTy) (NestJoin joinPred) xs ys'
  where
    xTy        = elemT $ typeOf xs
    yTy        = elemT $ typeOf ys
    ys' = case fromList yPreds of
              Just ps -> Comp (ListT yTy) (Var yTy y) (BindQ y ys :* fmap GuardQ ps)
              Nothing -> ys

-- | Search qualifiers for a generator for which we can unnest from the
-- comprehension head.
unnestSpineHeadT :: Expr -> TransformC CL (NL Qual, Expr)
unnestSpineHeadT h = readerT $ \cl -> case cl of
    QualsCL (BindQ x xs :* qs) -> do
        let xTy = elemT $ typeOf xs
        (Just ((joinName, ys), joinPred, yGuards), h') <- statefulT Nothing $ childT QualsTail $ traverseToHeadT S.empty (x, xTy) h
        let yTy        = elemT $ typeOf ys
        scopeNames <- S.insert x <$> S.fromList <$> inScopeNames <$> contextT
        let (qs', h'') = substCompE scopeNames x (P.fst $ Var (nestJoinElemTy xTy yTy) joinName) qs h'
        pure (BindQ joinName (mkJoin xs ys joinPred yGuards) :* qs', h'')
    QualsCL (S (BindQ x xs))   -> do
        let xTy = elemT $ typeOf xs
        ctx <- contextT
        let ctx' = ctx { clBindings = M.insert x (elemT $ typeOf xs) (clBindings ctx) }
        (Just ((joinName, ys), joinPred, yGuards), hCl) <- statefulT Nothing $ constT (pure $ inject h) >>> withContextT ctx' (searchHeadR S.empty (x, xTy))
        let yTy        = elemT $ typeOf ys
        scopeNames <- S.insert x <$> S.fromList <$> inScopeNames <$> contextT
        h' <- projectM hCl
        let h'' = substE scopeNames x (P.fst $ Var (nestJoinElemTy xTy yTy) joinName) h'
        pure (S (BindQ joinName (mkJoin xs ys joinPred yGuards)), h'')
    QualsCL (GuardQ _ :* _)    -> childT QualsTail $ unnestSpineHeadT h
    _                          -> fail "no match"

--------------------------------------------------------------------------------
-- Unnesting from a comprehension head

-- We unnest only one comprehension at a time.
--
-- General rule:
-- [ e x [ f x y | y <- ys, jp x y, p1 x, p2 x y, p3 y ] | qs, x <- xs, qs' ]
-- =>
-- [ e u.1 [ f y.1 y.2 | v <- u.2, p1 v.1, p2 v.1 v.2 ]
-- | qs, u <- xs △_jp [ y | y <- ys, p3 y, qs'[u.1/x] ]
-- ]
--
-- Predicates on the inner comprehension that only refer to y can be
-- safely evaluated before joining. Note that predicates on the inner
-- comprehension that only refer to x can **not** be evaluated on xs
-- alone!

unnestHeadR :: RewriteC CL
unnestHeadR = do
    Comp t h _ <- promoteT idR
    (qs', h') <- childT CompQuals $ unnestSpineHeadT h
    pure $ inject $ Comp t h' qs'

--------------------------------------------------------------------------------
-- Unnesting from a comprehension head

-- | Try to unnest comprehensions from subsequent guards and qualifiers, which
-- we can not unnest otherwise (e.g. by introduing semi- or antijoins).
--
--   [ e | qs, x <- xs, qs', p [ e' | y <- ys, jp x y, p y, e'' ], qs'' ]
--
-- rewrites into
--
--   [ e[u.1/x] |
--   | qs
--   , u <- xs nestjoin(jp) [ y | y <- ys, p y ]
--   , qs'[u.1/x]
--   , p u.1 [ e'[v.1/x][v.2/y] | v <- u.2, e''[v.1/x][v.2/y] ]
--   , qs''[u.1/x]
--   ]
--
-- Additional predicates on the inner comprehension are handled in the
-- same way as in unnesting from a comprehension head.

unnestQualsR' :: RewriteC CL
unnestQualsR' = do
    Comp t h _ <- promoteT idR
    (qs', h') <- childT CompQuals $ unnestSpineQualsT h
    pure $ inject $ Comp t h' qs'

-- | Search qualifiers for a generator for which we can unnest from the
-- from remaining qualifiers.
unnestSpineQualsT :: Expr -> TransformC CL (NL Qual, Expr)
unnestSpineQualsT h = readerT $ \cl -> case cl of
    QualsCL (BindQ x xs :* _) -> do
        let xTy = elemT $ typeOf xs
        (Just ((joinName, ys), joinPred, yGuards), qsCl) <- statefulT Nothing $ childT QualsTail $ searchQualsR S.empty (x, xTy)
        let yTy        = elemT $ typeOf ys
        scopeNames <- S.insert x <$> S.fromList <$> inScopeNames <$> contextT
        qs' <- constT $ projectM qsCl
        let (qs'', h') = substCompE scopeNames x (P.fst $ Var (nestJoinElemTy xTy yTy) joinName) qs' h
        pure (BindQ joinName (mkJoin xs ys joinPred yGuards) :* qs'', h')
    QualsCL (GuardQ _ :* _)    -> childT QualsTail $ unnestSpineQualsT h
    _ -> fail "no match"
