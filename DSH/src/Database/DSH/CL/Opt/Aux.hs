{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE LambdaCase       #-}

-- | Common tools for rewrites
module Database.DSH.CL.Opt.Aux 
    ( applyExpr
    , applyT
      -- * Monad rewrites with additional state
    , TuplifyM
      -- * Converting predicate expressions into join predicates
    , splitJoinPredT
      -- * Moving predicates towards the front of a qualifier list.
    , isSimplePred
    , pushSimpleFilters
    , pushEquiFilters
    , pushSemiFilters
    , pushAntiFilters
      -- * Free and bound variables
    , freeVars
    , compBoundVars
      -- * Substituion
    , substR
    , tuplifyR
      -- * NL spine traversal
    , onetdSpineT
      -- * Debugging
    , debug
    , debugUnit
    , debugOpt
    , debugPipeR
    , debugTrace
    , debugShow
    ) where
    
import           Control.Arrow
import qualified Data.Foldable as F
import           Data.List
import           Debug.Trace

import           Language.KURE                 
import           Language.KURE.Debug

import           Database.DSH.Impossible
import           Database.DSH.CL.Lang
import           Database.DSH.CL.Kure
import           Database.DSH.CL.Monad

-- | A version of the CompM monad in which the state contains an additional
-- rewrite. Use case: Returning a tuplify rewrite from a traversal over the
-- qualifier list so that it can be applied to the head expression.
type TuplifyM = CompSM (RewriteC CL)

-- | Run a translate on an expression without context
applyExpr :: TranslateC CL b -> Expr -> Either String b
applyExpr f e = runCompM $ apply f initialCtx (inject e)

-- | Run a translate on any value which can be injected into CL
applyT :: Injection a CL => TranslateC CL b -> a -> Either String b
applyT t e = runCompM $ apply t initialCtx (inject e)
          

--------------------------------------------------------------------------------
-- Rewrite general expressions into equi-join predicates

toJoinExpr :: Ident -> TranslateC Expr JoinExpr
toJoinExpr n = do
    e <- idR
    
    let prim1 :: (Prim1 a) -> TranslateC Expr UnOp
        prim1 (Prim1 Fst _) = return FstJ
        prim1 (Prim1 Snd _) = return SndJ
        prim1 (Prim1 Not _) = return NotJ
        prim1 _             = fail "toJoinExpr: primitive can't be translated to join primitive"
        
    case e of
        AppE1 _ p _   -> do
            p' <- prim1 p
            appe1T (toJoinExpr n) (\_ _ e1 -> UnOpJ p' e1)
        BinOp _ _ _ _ -> do
            binopT (toJoinExpr n) (toJoinExpr n) (\_ o e1 e2 -> BinOpJ o e1 e2)
        Lit _ v       -> do
            return $ ConstJ v
        Var _ x       -> do
            guardMsg (n == x) "toJoinExpr: wrong name"
            return InputJ
        _             -> do
            fail "toJoinExpr: can't translate to join expression"
            
-- | Try to transform an expression into an equijoin predicate. This will fail
-- if either the expression does not have the correct shape (equality with
-- simple projection expressions on both sides) or if one side of the predicate
-- has free variables which are not the variables of the qualifiers given to the
-- function.
splitJoinPredT :: Ident -> Ident -> TranslateC Expr (JoinExpr, JoinExpr)
splitJoinPredT x y = do
    BinOp _ Eq e1 e2 <- idR

    let fv1 = freeVars e1
        fv2 = freeVars e2
        
    if [x] == fv1 && [y] == fv2
        then binopT (toJoinExpr x) (toJoinExpr y) (\_ _ e1' e2' -> (e1', e2'))
        else if [y] == fv1 && [x] == fv2
             then binopT (toJoinExpr y) (toJoinExpr x) (\_ _ e1' e2' -> (e2', e1'))
             else fail "splitJoinPredT: not an equi-join predicate"

---------------------------------------------------------------------------------
-- Pushing filters towards the front of a qualifier list

-- | Push guards as far as possible towards the front of the qualifier
-- list. Predicate 'mayPush' decides wether a guard might be pushed at all. The
-- rewrite fails if no guard can be pushed.
pushFilters :: ([Ident] -> Expr -> Bool) -> RewriteC Expr
pushFilters mayPush = do
    Comp _ _ _ <- idR
    compR idR (pushFiltersQuals mayPush)

pushFiltersQuals :: ([Ident] -> Expr -> Bool) -> RewriteC (NL Qual)
pushFiltersQuals mayPush = do
    (reverseNL . initFlags mayPush)
      ^>> checkSuccess
      -- FIXME using innermostR here is really inefficient!
      >>> innermostR tryPush 
      >>^ (reverseNL . fmap snd)
      
-- | Fail if no guard can be pushed
checkSuccess :: RewriteC (NL (Bool, Qual))
checkSuccess = do
    qs <- idR
    if (any fst $ toList qs)
        then (return qs)
        else (trace "checkSuccess" $ fail "no guards can be pushed")
    
-- Mark all guards which may be pushed based on a general predicate
-- `mayPush`. To this predicate, we pass the guard expression as well as the
-- list of identifiers which are in scope for the current guard.
initFlags :: ([Ident] -> Expr -> Bool) -> NL Qual -> NL (Bool, Qual)
initFlags mayPush qs = 
    case fromList flaggedQuals of
        Just qs' -> qs'
        Nothing  -> $impossible
  where
    flaggedQuals = reverse
                   $ snd
                   $ foldl' (flagQualifiers mayPush) (Nothing, []) 
                   $ zip localScopes (toList qs)

    localScopes = map compBoundVars $ inits $ toList qs

    
-- | For each guard, decide wether it may be pushed or not and mark it
-- accordingly. If a guard is located directly next to a generator
-- binding a variable which occurs free in the guard, it is marked
-- unpushable without looking at it further.
flagQualifiers 
  :: ([Ident] -> Expr -> Bool)
  -> (Maybe Ident, [(Bool, Qual)]) 
  -> ([Ident], Qual) 
  -> (Maybe Ident, [(Bool, Qual)])
flagQualifiers mayPush (mPrevBind, flaggedQuals) (localScope, qual) =
    case (mPrevBind, qual) of
        -- No generator left of the guard. Only look at the guard
        -- itself.
        (Nothing, GuardQ p) -> 
            (Nothing, (mayPush localScope p, qual) : flaggedQuals)

        -- Guard is located left of a generator which binds one guard
        -- expression variable. It must not be pushed.
        (Just x, GuardQ p) | x `elem` freeVars p -> 
            (Nothing, (False, qual) : flaggedQuals)

        -- There is a generator left of the guard, but the bound
        -- variable does not occur in the guard expression.
        (Just _, GuardQ p) | otherwise           -> 
            (Nothing, (mayPush localScope p, qual) : flaggedQuals)
            
        -- Generators are never pushed. Just hand the bound variable to
        -- the next qualifier.
        (_, BindQ x _) -> 
            (Just x, (False, qual) : flaggedQuals)
                       
tryPush :: RewriteC (NL (Bool, Qual))
tryPush = do
    qualifiers <- idR 
    case qualifiers of
        q1@(True, GuardQ p) :* q2@(_, BindQ x _) :* qs ->
            if x `elem` freeVars p
            -- We can't push through the generator because it binds a
            -- variable we depend upon
            then return $ (False, GuardQ p) :* q2 :* qs
               
            -- We can push
            else return $ q2 :* q1 :* qs
            
        q1@(True, GuardQ _) :* q2@(_, GuardQ _) :* qs  ->
            return $ q2 :* q1 :* qs

        (True, GuardQ p) :* (S q2@(_, BindQ x _))      ->
            if x `elem` freeVars p
            then return $ (False, GuardQ p) :* (S q2)
            else return $ q2 :* (S (False, GuardQ p))

        (True, GuardQ p) :* (S q2@(_, GuardQ _))       ->
            return $ q2 :* (S (False, GuardQ p))

        (True, BindQ _ _) :* _                         ->
            error "generators can't be pushed"

        (False, _) :* _                                ->
            fail "can't push: node marked as unpushable"

        S (True, q)                                    ->
            return $ S (False, q)

        S (False, _)                                   ->
            fail "can't push: already at front"


isEquiJoinPred :: [Ident] -> Expr -> Bool
isEquiJoinPred locallyBoundVars (BinOp _ Eq e1 e2) = 
    isProj e1 
    && isProj e2
    && length fv1 == 1
    && length fv2 == 1
    && fv1 /= fv2
    
    -- For an equi join predicate which we would like to push, only variables
    -- bound by local generators might occur. This restriction should avoid the
    -- case that a predicate which correlates with an outer comprehension blocks
    -- a local equijoin predicate from being pushed next to its generators.
    && (fv1 ++ fv2) `subset` locallyBoundVars

  where fv1 = freeVars e1
        fv2 = freeVars e2
        
        subset :: Eq a => [a] -> [a] -> Bool
        subset as bs = all (\a -> any (== a) bs) as
isEquiJoinPred _ _                  = False

isProj :: Expr -> Bool
isProj (AppE1 _ (Prim1 Fst _) e) = isProj e
isProj (AppE1 _ (Prim1 Snd _) e) = isProj e
isProj (AppE1 _ (Prim1 Not _) e) = isProj e
isProj (BinOp _ _ e1 e2)         = isProj e1 && isProj e2
isProj (Var _ _)                 = True
isProj _                         = False

-- | Does the predicate look like an existential quantifier and is eligible for
-- pushing? Note: In addition to the variables that are bound by the current
-- qualifier list, we need to pass the variable bound by the existential
-- comprehension to isEquiJoinPred, because it might (and should) occur in the
-- predicate.
isSemiJoinPred :: [Ident] -> Expr -> Bool
isSemiJoinPred vs (AppE1 _ (Prim1 Or _) 
                           (Comp _ p 
                                   (S (BindQ x _)))) = isEquiJoinPred (x : vs) p
isSemiJoinPred _  _                                  = False

isAntiJoinPred :: [Ident] -> Expr -> Bool
isAntiJoinPred vs (AppE1 _ (Prim1 And _) 
                           (Comp _ p
                                   (S (BindQ x _)))) = isEquiJoinPred (x : vs) p
isAntiJoinPred _  _                                  = False

-- 'Simple' currently simply means 'does not contain a comprehension'.
isSimplePred :: Expr -> Bool
isSimplePred e = 
  case applyExpr t e of
     Left _   -> True
     Right b  -> b
        
  where
    t :: TranslateC CL Bool
    t = onetdT $ do
        Comp _ _ _ <- promoteT idR
        return False

pushEquiFilters :: RewriteC Expr
pushEquiFilters = pushFilters isEquiJoinPred
       
pushSemiFilters :: RewriteC Expr
pushSemiFilters = pushFilters isSemiJoinPred

pushAntiFilters :: RewriteC Expr
pushAntiFilters = pushFilters isAntiJoinPred

pushAllFilters :: RewriteC Expr
pushAllFilters = pushFilters (\_ _ -> True)

pushSimpleFilters :: RewriteC Expr
pushSimpleFilters = pushFilters (\_ -> isSimplePred)


--------------------------------------------------------------------------------
-- Computation of free variables

freeVarsT :: TranslateC CL [Ident]
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
               v' <- constT $ freshName (inScopeVars ctx)
               let varTy = domainT lamTy
               lamT (extractR $ tryR $ substR v (Var varTy v')) (\_ _ -> Lam lamTy v')
              
nonBinder :: Expr -> Bool
nonBinder expr =
    case expr of
        Lam _ _ _  -> False
        Var _ _    -> False
        Comp _ _ _ -> False
        _          -> True
                                                
substR :: Ident -> Expr -> RewriteC CL
substR v s = readerT $ \case
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
-- Traversal functions

-- | Traverse the spine of a NL list top-down and apply the translation as soon
-- as possible.
onetdSpineT 
  :: (ReadPath c Int, MonadCatch m, Walker c CL) 
  => Translate c m CL b 
  -> Translate c m CL b
onetdSpineT t = do
    n <- idR
    case n of
        QualsCL (_ :* _) -> childT 0 t <+ childT 1 (onetdSpineT t)
        QualsCL (S _)    -> childT 0 t
        _                -> $impossible

--------------------------------------------------------------------------------
-- Simple debugging combinators
           
debug :: Show a => String -> a -> b -> b
debug msg a b =
    trace ("\n" ++ msg ++ " =>\n" ++ show a) b

debugUnit :: (Show a, Monad m) => String -> a -> m ()
debugUnit msg a = debug msg a (return ())

debugOpt :: Expr -> Either String Expr -> Expr
debugOpt origExpr mExpr =
    trace (showOrig origExpr)
    $ either (flip trace origExpr) (\e -> trace (showOpt e) e) mExpr
    
  where 
    showOrig :: Expr -> String
    showOrig e =
        "\nOriginal query ====================================================================\n"
        ++ show e 
        ++ "\n==================================================================================="
        
    showOpt :: Expr -> String
    showOpt e =
        "Optimized query ===================================================================\n"
        ++ show e 
        ++ "\n===================================================================================="
        
debugPipeR :: (Monad m, Show a) => Rewrite c m a -> Rewrite c m a
debugPipeR r = debugR 1000 "Before >>>>>>"
               >>> r
               >>> debugR 1000 ">>>>>>> After"
               
debugTrace :: Monad m => String -> Rewrite c m a
debugTrace msg = trace msg idR

debugShow :: (Monad m, Show a) => String -> Rewrite c m a
debugShow msg = debugR 10000 (msg ++ "\n")
