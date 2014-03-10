{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE LambdaCase          #-}
    
-- | Deal with nested comprehensions by introducing explicit nesting
-- operators (NestJoin, NestProduct).
module Database.DSH.CL.Opt.NestJoin
  ( nestjoinR
  ) where
  
import           Control.Applicative((<$>))
import           Control.Arrow

import           Data.Either
import qualified Data.Foldable as F
import           Data.List
import           Data.List.NonEmpty(NonEmpty((:|)), (<|))
import qualified Data.List.NonEmpty as N
import qualified Data.Set as S
import qualified Data.Map as M

import           Database.DSH.Impossible

import           Database.DSH.CL.Lang
import           Database.DSH.CL.Kure
                 
import qualified Database.DSH.CL.Primitives as P

import           Database.DSH.CL.Opt.Aux

nestjoinR :: RewriteC CL
nestjoinR = unnestFromGuardR <+ unnestFromHeadR

--------------------------------------------------------------------------------
-- Common code for unnesting from a comprehension head and from
-- comprehension guards

type HeadExpr = Either PathC (PathC, Type, Expr, NL Qual) 

-- A representation of a nested comprehension which is eligible for
-- unnesting
data NestedComp = NestedComp
    { hType   :: Type
    , hHead   :: Expr
    , hGen    :: (Ident, Expr)
    , hGuards :: [Expr]
    }

-- | Search for a comprehension in an outer comprehension's head that
-- is eligible for unnesting. 'x' is the outer comprehension's
-- generator variable and must not occur in the generator of the inner
-- comprehension. The inner comprehension must feature only one
-- generator.

fromGuard :: Monad m => Qual -> m Expr
fromGuard (GuardQ e)  = return e
fromGuard (BindQ _ _) = fail "not a guard"

-- FIXME don't descend into comprehensions, or lambdas!
searchNestedCompT :: Ident -> TranslateC CL (PathC, NestedComp)
searchNestedCompT x = 
    onetdT $ do
        Comp t h qs <- promoteT idR
        (y, ys, qsr) <- case qs of
            S (BindQ y ys)    -> return (y, ys, [])
            BindQ y ys :* qsr -> return (y, ys, toList qsr)
            _                 -> fail "no match"

        guardM $ not $ x `elem` freeVars ys
        guards <- constT $ mapM fromGuard qsr

        p <- snocPathToPath <$> absPathT
        return (p, NestedComp t h (y, ys) guards)

-- | Take an absolute path and drop the prefix of the path to a direct child of
-- the current node. This makes it a relative path starting from **some** direct
-- child of the current node.
relativePathT :: Path a -> TranslateC b (Path a)
relativePathT p = do
    curPath <- snocPathToPath <$> absPathT
    return $ drop (1 + length curPath) p

constNodeT :: (Injection a CL, Monad m) => a -> Translate c m b CL
constNodeT expr = constT $ return $ inject expr

-- | Transform a suitable comprehension that was either nested in a
-- comprehension head or in a guard expression and the corresponding
-- outer generator.
unnestWorkerT
  :: NestedComp                   -- ^ The nested comprehension
  -> (Ident, Expr)                -- ^ The outer generator
  -> TranslateC CL ( Expr         -- ^ Return replacement for the inner comprehension,
                   , Expr         -- outer generator with nesting op
                   , RewriteC CL  -- and the tuplify rewrite for the outer generator variable.
                   )
unnestWorkerT headComp (x, xs) = do
    let (y, ys) = hGen headComp

    let (joinPredCandidates, nonJoinPreds) = partition (isEquiJoinPred x y) 
                                                       (hGuards headComp)

    -- Determine which operator to use to implement the nesting. If
    -- there is a join predicate, we use a nestjoin. Only if there is
    -- no matching join predicate, we use a nested cartesian product
    -- (nestproduct).
    -- FIXME include all join predicates on the join operator
    (nestOp, remJoinPreds) <- case joinPredCandidates of
        [] -> return (NestProduct, [])
        p : ps -> do
            -- Split the join predicate
            (leftExpr, rightExpr) <- constT (return p) >>> splitJoinPredT x y
            return (NestJoin leftExpr rightExpr, ps)

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

    innerVar <- freshNameT

    let tuplifyInnerVarR :: Expr -> TranslateC CL Expr
        tuplifyInnerVarR e = constT (return $ inject e) 
                            >>> tuplifyR innerVar (x, xt) (y, yt)
                            >>> projectT

    -- In the head of the inner comprehension, replace x and y
    -- with the corresponding pair components of the inner lists
    -- in the join result.
    h' <- tuplifyInnerVarR (hHead headComp)

    -- Do the same on left over predicates, which will be
    -- evaluated on the nestjoin result.
    remPreds <- sequence $ map tuplifyInnerVarR (remJoinPreds ++ leftOverPreds)
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
type GuardM = CompSM (RewriteC CL, Maybe Expr)


-- | Search for an eligible nested comprehension in the current guard
-- and unnest it. Returns the tuplifying rewrite for the outer
-- generator variable 'x', the new generator with the nesting
-- operator, and the modified predicate.
unnestGuardT :: (Ident, Expr) -> Expr -> TranslateC CL (RewriteC CL, Expr, Expr)
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
unnestGuardR :: [Expr] -> [Expr] -> TranslateC CL (CL, [Expr], [Expr])
unnestGuardR candGuards failedGuards = do
    Comp t _ _      <- promoteT idR 
    let unnestR = anytdR (promoteR unnestQualsR) >>> projectT
    ((tuplifyR, Just guardExpr), qs') <- statefulT (idR, Nothing) $ childT CompQuals unnestR
                                       
    h'              <- childT CompHead tuplifyR >>> projectT
    let tuplifyM e = constNodeT e >>> tuplifyR >>> projectT
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
    ExprCL (Comp ty h qs) <- return comp'
    return (C ty h qs, candGuards', failedGuards')

unnestFromGuardR :: RewriteC CL
unnestFromGuardR = mergeGuardsIterR unnestGuardWorkerR
