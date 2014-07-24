{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE QuasiQuotes           #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
    
-- | Deal with nested comprehensions by introducing explicit nesting
-- operators (NestJoin, NestProduct).
module Database.DSH.CL.Opt.NestJoin
  ( nestjoinR
  , zipCorrelatedR
  , nestingGenR
  ) where

import           Control.Applicative((<$>))
import           Control.Arrow
import           Control.Monad

import           Data.List
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.List.NonEmpty as N

import           Database.DSH.Common.Lang

import           Database.DSH.CL.Lang
import           Database.DSH.CL.Kure
                 
import qualified Database.DSH.CL.Primitives as P

import           Database.DSH.CL.Opt.Aux

nestjoinR :: RewriteC CL
nestjoinR = unnestFromGuardR <+ unnestFromHeadR

--------------------------------------------------------------------------------
-- Common code for unnesting from a comprehension head and from
-- comprehension guards

-- A representation of a nested comprehension which is eligible for
-- unnesting
data NestedComp = NestedComp
    { hType   :: Type
    , hHead   :: Expr
    , hGen    :: (Ident, Expr)
    , hGuards :: [Expr]
    }


-- | Check if a comprehension is eligible for unnesting. This is the
-- case if the outer generator variable 'x' does not occur in the
-- inner generator and if there is only one inner generator.
nestedCompT :: Ident -> TransformC CL (PathC, NestedComp)
nestedCompT x = do
    Comp t h qs <- promoteT idR
    (y, ys, qsr) <- case qs of
        S (BindQ y ys)    -> return (y, ys, [])
        BindQ y ys :* qsr -> return (y, ys, toList qsr)
        _                 -> fail "no match"

    guardM $ not $ x `elem` freeVars ys
    guards <- constT $ mapM fromGuard qsr

    p <- snocPathToPath <$> absPathT
    return (p, NestedComp t h (y, ys) guards)

-- | Traverse though an expression and search for a comprehension that
-- is eligible for unnesting.
searchNestedCompT :: Ident -> TransformC CL (PathC, NestedComp)
searchNestedCompT x =
    readerT $ \e -> case e of
        ExprCL Comp{} -> nestedCompT x
        ExprCL Lam{}  -> fail "don't descent into lambdas"
        ExprCL _      -> oneT $ searchNestedCompT x
        _             -> fail "only traverse through expressions"
        

-- | Take an absolute path and drop the prefix of the path to a direct child of
-- the current node. This makes it a relative path starting from **some** direct
-- child of the current node.
relativePathT :: Path a -> TransformC b (Path a)
relativePathT p = do
    curPath <- snocPathToPath <$> absPathT
    return $ drop (1 + length curPath) p

constNodeT :: (Injection a CL, Monad m) => a -> Transform c m b CL
constNodeT expr = constT $ return $ inject expr

-- | Transform a suitable comprehension that was either nested in a
-- comprehension head or in a guard expression and the corresponding
-- outer generator. Returns a replacement for the inner comprehension,
-- outer generator with nesting op and the tuplify rewrite for the
-- outer generator variable.
unnestWorkerT
  :: NestedComp                   -- ^ The nested comprehension
  -> (Ident, Expr)                -- ^ The outer generator
  -> TransformC CL (Expr, Expr, RewriteC CL)
unnestWorkerT headComp (x, xs) = do
    let (y, ys) = hGen headComp

    -- Generators have to be indepedent
    guardM $ x `notElem` freeVars ys

    let (joinPredCandidates, nonJoinPreds) = partition (isThetaJoinPred x y) 
                                                       (hGuards headComp)

    -- Determine which operator to use to implement the nesting. If
    -- there is a join predicate, we use a nestjoin. Only if there is
    -- no matching join predicate, we use a nested cartesian product
    -- (nestproduct).
    -- FIXME include all join predicates on the join operator
    nestOp <- case joinPredCandidates of
        [] -> return NestProduct
        p : ps -> do
            -- Split the join predicate
            p'  <- constT (return p) >>> splitJoinPredT x y
            ps' <- constT (return ps) >>> mapT (splitJoinPredT x y)
           
            return $ NestJoin $ JoinPred $ p' N.:| ps'

    -- Identify predicates which only refer to y and can be evaluated
    -- on the right nestjoin input.
    let (yPreds, leftOverPreds) = partition ((== [y]) . freeVars) nonJoinPreds

    -- Left over we have predicates which (propably) refer to both
    -- x and y and are not/can not be used as the join predicate.
    --    [ [ e x y | y <- ys, p x y, p' x y ] | x <- xs ]
    -- => [ [ e [fst y/x][snd y/y] | y <- snd x, p'[fst y/x][snd y/y] ] | x <- xs nj(p) ys ]
  
    let xt       = elemT $ typeOf xs
        yt       = elemT $ typeOf ys
        tupType  = pairT xt (listT (pairT xt yt))
        joinType = listT xt .-> (listT yt .-> listT tupType)
        joinVar  = Var tupType x
        
    -- If there are inner predicates which only refer to y,
    -- evaluate them on the right (ys) nestjoin input.
    let ys' = case fromList yPreds of
                  Just ps -> Comp (listT yt) (Var yt y) (BindQ y ys :* fmap GuardQ ps)
                  Nothing -> ys

    -- the nesting operator combining xs and ys: 
    -- xs nj(p) ys
    let xs'        = AppE2 (listT tupType) (Prim2 nestOp joinType) xs ys'

    innerVar <- freshNameT []

    let tuplifyInnerVarR :: Expr -> TransformC CL Expr
        tuplifyInnerVarR e =  constNodeT e
                              >>> tuplifyR innerVar (x, xt) (y, yt)
                              >>> projectT

    -- In the head of the inner comprehension, replace x and y
    -- with the corresponding pair components of the inner lists
    -- in the join result.
    h' <- tuplifyInnerVarR (hHead headComp)

    -- Do the same on left over predicates, which will be
    -- evaluated on the nestjoin result.
    remPreds <- sequence $ map tuplifyInnerVarR leftOverPreds
    let remGuards = map GuardQ remPreds

    -- Construct the inner comprehension with the tuplified head
    -- and apply left-over predicates to the inner comprehension.
    let ti = hType headComp
    let headComp' = case remGuards of
            g : gs -> Comp ti h' (BindQ innerVar (P.snd joinVar) :* fromListSafe g gs)
            []     -> Comp ti h' (S $ BindQ innerVar (P.snd joinVar))

    let tuplifyOuterR :: RewriteC CL
        tuplifyOuterR = substR x $ P.fst joinVar

    return (headComp', xs', tuplifyOuterR)


--------------------------------------------------------------------------------
-- Unnesting from a comprehension head

-- In constrast to the previous strategy, we unnest only one
-- comprehension at a time. We unnest from the original comprehension
-- head, without normalizing it first. This saves quite a lot of
-- rather complex rewrites for normalizing the head and combining
-- multiple nesting operators. The resulting plans look the same.

-- General rule:
-- [ e x [ f x y | y <- ys, jp x y, p1 x, p2 x y, p3 y ] | x <- xs, p4 x ]
-- =>
-- [ e (fst x) [ f (fst y) (snd y) 
--             | y <- snd x
--             , p1 (fst y)
--             , p2 (fst y) (snd y)
--             ]
-- | x <- xs △_jp [ y | y <- ys, p3 y ]
-- ]
-- 
-- In the absence of a proper join predicate, we use the Nestproduct 
-- operator ▽ instead of NestJoin.
--
-- Predicates on the inner comprehension that only refer to y can be
-- safely evaluated before joining. Note that predicates on the inner
-- comprehension that only refer to x can **not** be evaluated on xs
-- alone!

-- | Search for one comprehension nested in a comprehension head,
-- extract it and transform it into a nesting operator.
unnestFromHeadR :: RewriteC CL
unnestFromHeadR = do
    Comp to ho qso <- promoteT idR

    -- We need one generator on a comprehension
    (x, xs, qsr) <- case qso of
                        S (BindQ x xs)    -> return (x, xs, [])
                        BindQ x xs :* qsr -> return (x, xs, toList qsr)
                        _                 -> fail "no match"

    -- More precisely, we need *exactly one* generator on the
    -- comprehension
    guardM $ all isGuard qsr
    
    (headCompPath, headComp) <- childT CompHead (searchNestedCompT x)

    (headComp', nestOp, tuplifyOuterR) <- unnestWorkerT headComp (x, xs)

    -- Insert the replacement for the nested comprehension.
    
    -- The relative path to the comprehension to be replaced, starting
    -- from the head expression
    -- FIXME use withLocalPathT
    relCompPath <- relativePathT headCompPath

    ExprCL tuplifiedHo <- constNodeT ho >>> tryR tuplifyOuterR
    ExprCL unnestedHo  <- constNodeT tuplifiedHo >>> pathR relCompPath (constNodeT headComp')

    -- In the outer comprehension's qualifier list, x is replaced by
    -- the first pair component of the join result.
    qsr' <- constT (return $ map inject qsr)
            >>> mapT (tryR tuplifyOuterR) 
            >>> mapT projectT

    -- ExprCL tuplifiedHead <- constNodeT ho' >>> tryR tuplifyOuterR

    return $ inject $ Comp to unnestedHo (fromListSafe (BindQ x nestOp) qsr')

    
--------------------------------------------------------------------------------
-- Nestjoin introduction: unnesting comprehensions from complex predicates

-- | Try to unnest comprehensions from guards, which we can not unnest otherwise
-- (e.g. by introduing semi- or antijoins).
-- 
--   [ e | qs, x <- xs, p x [ f x y | y < ys jp x y ], qs' ]
-- 
-- rewrites into
--
--   [ e[fst x/x] | 
--   | qs
--   , x <- xs nestjoin(jp) ys
--   , p (fst x) [ f (fst y) (snd y) | y <- snd x ]
--   , qs'[fst x/x]
--   ]
--
-- Additional predicates on the inner comprehension are handled in the
-- same way as in unnesting from a comprehension head.

-- | Store not only the tuplifying rewrite in the state, but also the
-- rewritten guard expression.
-- FIXME this is a rather ugly hack
type GuardM = RewriteStateM (RewriteC CL, Maybe Expr)


-- | Search for an eligible nested comprehension in the current guard
-- and unnest it. Returns the tuplifying rewrite for the outer
-- generator variable 'x', the new generator with the nesting
-- operator, and the modified predicate.
unnestGuardT :: (Ident, Expr) -> Expr -> TransformC CL (RewriteC CL, Expr, Expr)
unnestGuardT (x, xs) guardExpr = do
    -- search for an unnestable comrehension
    (headCompPath, headComp) <- withLocalPathT 
                                $ constNodeT guardExpr >>> searchNestedCompT x

    -- combine inner and outer comprehension
    (headComp', nestOp, tuplifyOuterR) <- unnestWorkerT headComp (x, xs)

    -- Tuplify occurences of 'x' in the guard.
    ExprCL tuplifiedGuardExpr <- constNodeT guardExpr 
                                 >>> tryR tuplifyOuterR

    -- Insert the new inner comprehension into the original guard
    -- expression
    ExprCL simplifiedGuardExpr <- constNodeT tuplifiedGuardExpr 
                                  >>> pathR headCompPath (constNodeT headComp')


    return (tuplifyOuterR, nestOp, simplifiedGuardExpr)
    
-- | Search for unnestable combinations of a generator and a nested
-- guard in a qualifier list.
unnestQualsR :: Rewrite CompCtx GuardM (NL Qual)
unnestQualsR = do
    readerT $ \case
        -- In the middle of a qualifier list
        BindQ x xs :* GuardQ p :* qs -> do
            (tuplifyHeadR, xs', p') <- liftstateT $ constNodeT p >>> unnestGuardT (x, xs) p
            constT $ modify (\(r, _) -> (r >>> tuplifyHeadR, Just p'))
            qs' <- liftstateT $ constNodeT qs >>> tuplifyHeadR >>> projectT
            return $ BindQ x xs' :* qs'

        -- At the end of a qualifier list
        BindQ x xs :* (S (GuardQ p)) -> do
            (tuplifyHeadR, xs', p') <- liftstateT $ constNodeT p >>> unnestGuardT (x, xs) p
            constT $ modify (\(r, _) -> (r >>> tuplifyHeadR, Just p'))
            return $ S $ BindQ x xs'
        _ -> fail "no match"

-- | Trigger the search for unnesting opportunities in the qualifier
-- list and tuplify comprehension head and remaining qualifiers on
-- success.
-- 
-- Note: In contrast to e.g. flat join introduction, we can't merge
-- the complete guard into the operator. The non-comprehension part
-- remains. We handle this by including the succesfully unnested and
-- modified guard in the list of failed guard expressions, even on
-- success.
unnestGuardR :: [Expr] -> [Expr] -> TransformC CL (CL, [Expr], [Expr])
unnestGuardR candGuards failedGuards = do
    Comp t _ _      <- promoteT idR 
    let unnestR = anytdR (promoteR unnestQualsR) >>> projectT
    ((tuplifyVarR, Just guardExpr), qs') <- statefulT (idR, Nothing) $ childT CompQuals unnestR
                                       
    h'              <- childT CompHead tuplifyVarR >>> projectT
    let tuplifyM e = constNodeT e >>> tuplifyVarR >>> projectT
    candGuards'     <- mapM tuplifyM candGuards
    failedGuards'   <- mapM tuplifyM failedGuards
    return (inject $ Comp t h' qs', candGuards', guardExpr : failedGuards')

-- | Worker for the MergeGuard iterator: Insert the current guard into
-- the qualifier list and search for an unnesting opportunity.
unnestGuardWorkerR :: MergeGuard
unnestGuardWorkerR comp guardExpr candGuards failedGuards = do
    let C ty h qs = comp
    env <- S.fromList <$> M.keys <$> cl_bindings <$> contextT
    let compWithGuard = constT $ return $ ExprCL $ Comp ty h (insertGuard guardExpr env qs)
    (comp', candGuards', failedGuards') <- compWithGuard >>> unnestGuardR candGuards failedGuards
    ExprCL (Comp _ h' qs') <- return comp'
    return (C ty h' qs', candGuards', failedGuards')

unnestFromGuardR :: RewriteC CL
unnestFromGuardR = mergeGuardsIterR unnestGuardWorkerR


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

-- 

isComplexExpr :: Expr -> Bool
isComplexExpr e = 
    case e of
        Comp{}                   -> True
        If{}                     -> True
        App{}                    -> True
        BinOp{}                  -> True
        UnOp{}                   -> True
        Lam{}                    -> True
        AppE2 _ (Prim2 op _) _ _ -> complexPrim2 op
        AppE1 _ (Prim1 op _) _   -> complexPrim1 op
        Lit{}                    -> False
        Var{}                    -> False
        Table{}                  -> False

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
zipCorrelatedR = do
    Comp to (Comp ti e (S (BindQ y f))) (S (BindQ x xs)) <- promoteT idR
    
    let fvs = freeVars e 
    guardM $ x `elem` fvs && y `elem` fvs

    guardM $ x `elem` freeVars f

    -- Is f complex as required?
    void $ pathT [CompHead, CompQuals, QualsSingleton, BindQualExpr] containsComplexExprT

    z <- freshNameT [y]

    let genComp = Comp (listT $ typeOf f) f (S $ BindQ x xs)
        zipGen  = P.zip xs genComp
        zt      = elemT $ typeOf zipGen 
        zv      = Var zt z

    ExprCL f' <- constNodeT e >>> substR x (P.fst zv)

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
nestingGenR :: RewriteC CL
nestingGenR = do
    Comp  to (Comp ti e (S (BindQ y g))) (S (BindQ x xs)) <- promoteT idR
    
    -- Generator expression g should depend on x (otherwise we could
    -- unnest directly
    guardM $ x `elem` freeVars g

    -- Generator expression g should contain at least one unnestable
    -- comprehension
    void $ constNodeT g >>> searchNestedCompT x

    z <- freshNameT []

    let gty = typeOf g

    let innerComp = Comp ti e (S (BindQ y (Var gty z)))
        genComp   = Comp (listT gty) g (S (BindQ x xs))
        outerComp = Comp to innerComp (S (BindQ z genComp))

    return $ inject outerComp
