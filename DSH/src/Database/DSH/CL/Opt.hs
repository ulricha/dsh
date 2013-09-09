{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE TemplateHaskell     #-}
    
-- | This module performs optimizations on the Comprehension Language (CL).
module Database.DSH.CL.Opt 
  ( opt ) where
       
import           Debug.Trace
import           Text.Printf
                 
import           Control.Applicative((<$>))
import           Control.Arrow
-- import           Control.Monad

import           Data.Either
import           Data.List
import qualified Data.Map as M

import qualified Data.Foldable as F

import           Data.List.NonEmpty(NonEmpty((:|)), (<|))
import qualified Data.List.NonEmpty as N

-- import qualified Data.Set as S
-- import           GHC.Exts

import           Database.DSH.Impossible

-- import           Database.DSH.Impossible
   
import           Language.KURE.Debug

import           Database.DSH.CL.Lang
import           Database.DSH.CL.Kure
import           Database.DSH.CL.OptUtils

import qualified Database.DSH.CL.Primitives as P

--------------------------------------------------------------------------------
-- Pushing filters towards the front of a qualifier list

pushFilters :: ([Ident] -> Expr -> Bool) -> RewriteC Expr
pushFilters mayPush = do
    Comp _ _ qs <- idR
    compR idR pushFiltersQuals

  where
        
    pushFiltersQuals :: RewriteC (NL Qual)
    pushFiltersQuals = do
        (reverseNL . initFlags)
          -- FIXME using innermostR here is really inefficient!
          ^>> innermostR tryPush 
          >>^ (reverseNL . fmap snd)
        
    initFlags :: NL Qual -> NL (Bool, Qual)
    initFlags qs = 
        case fromList $ map flag $ zip localScopes (toList qs) of
            Just qs' -> qs'
            Nothing  -> $impossible
      where
        localScopes = map compBoundVars $ inits $ toList qs
        
        flag :: ([Ident], Qual) -> (Bool, Qual)
        flag (localScope, q@(BindQ _ _)) = (False, q)
        flag (localScope, q@(GuardQ p))  = (mayPush localScope p, q)
                
                       
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

isSemiJoinPred :: [Ident] -> Expr -> Bool
isSemiJoinPred vs (AppE1 _ (Prim1 Or _) (Comp _ p (S _))) = isEquiJoinPred vs p
isSemiJoinPred _  _                                       = False

isAntiJoinPred :: [Ident] -> Expr -> Bool
isAntiJoinPred vs (AppE1 _ (Prim1 And _) (Comp _ p (S _))) = isEquiJoinPred vs p
isAntiJoinPred _  _                                        = False

pushEquiFilters :: RewriteC Expr
pushEquiFilters = pushFilters isEquiJoinPred
       
pushSemiFilters :: RewriteC Expr
pushSemiFilters = pushFilters isSemiJoinPred

pushAntiFilters :: RewriteC Expr
pushAntiFilters = pushFilters isAntiJoinPred

pushAllFilters :: RewriteC Expr
pushAllFilters = pushFilters (\_ _ -> True)

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

--------------------------------------------------------------------------------
-- Introduce simple equi joins

type TuplifyM = CompSM (RewriteC CL)

-- | Concstruct an equijoin generator
mkeqjoinT 
  :: Expr  -- ^ The predicate
  -> Ident -- ^ Identifier from the first generator
  -> Ident -- ^ Identifier from the second generator
  -> Expr  -- ^ First generator expression
  -> Expr  -- ^ Second generator expression
  -> Translate CompCtx TuplifyM (NL Qual) (RewriteC CL, Qual)
mkeqjoinT pred x y xs ys = do
    -- The predicate must be an equi join predicate
    (leftExpr, rightExpr) <- constT (return pred) >>> (liftstateT $ splitJoinPredT x y)

    -- Conditions for the rewrite are fulfilled. 
    let xst          = typeOf xs
        yst          = typeOf ys
        xt           = elemT xst
        yt           = elemT yst
        pt           = listT $ pairT xt yt
        jt           = xst .-> (yst .-> pt)
        tuplifyHeadR = tuplifyR x (x, xt) (y, yt)
        joinGen      = BindQ x 
                         (AppE2 pt 
                           (Prim2 (EquiJoin leftExpr rightExpr) jt) 
                           xs ys)

    return (tuplifyHeadR, joinGen)

-- | Match an equijoin pattern in the middle of a qualifier list
eqjoinR :: Rewrite CompCtx TuplifyM (NL Qual)
eqjoinR = do
    -- We need two generators followed by a predicate
    BindQ x xs :* BindQ y ys :* GuardQ p :* qs <- promoteT idR
    
    (tuplifyHeadR, q') <- mkeqjoinT p x y xs ys
                               
    -- Next, we apply the tuplifyHeadR rewrite to the tail, i.e. to all following
    -- qualifiers
    -- FIXME why is extractT required here?
    qs' <- catchesT [ liftstateT $ (constT $ return qs) >>> (extractR tuplifyHeadR)
                    , constT $ return qs
                    ]            

    -- Combine the new tuplifying rewrite with the current rewrite by chaining
    -- both rewrites
    constT $ modify (>>> tuplifyHeadR)
    
    return $ q' :* qs'
    
-- | Matgch an equijoin pattern at the end of a qualifier list
eqjoinEndR :: Rewrite CompCtx TuplifyM (NL Qual)
eqjoinEndR = do
    -- We need two generators followed by a predicate
    BindQ x xs :* BindQ y ys :* (S (GuardQ p)) <- promoteT idR

    (tuplifyHeadR, q') <- mkeqjoinT p x y xs ys

    -- Combine the new tuplifying rewrite with the current rewrite by chaining
    -- both rewrites
    constT $ modify (>>> tuplifyHeadR)

    return (S q')

    
eqjoinQualsR :: Rewrite CompCtx TuplifyM (NL Qual) 
eqjoinQualsR = anytdR $ repeatR (eqjoinEndR <+ eqjoinR)
    
-- FIXME this should work without this amount of casting
-- FIXME and it should be RewriteC Expr
eqjoinCompR :: RewriteC CL
eqjoinCompR = do
    Comp t _ _          <- promoteT idR
    (tuplifyHeadR, qs') <- statefulT idR $ childT 1 (promoteR eqjoinQualsR >>> projectT)
    e'                  <- (tryR $ childT 0 tuplifyHeadR) >>> projectT
    return $ inject $ Comp t e' qs'

--------------------------------------------------------------------------------
-- Introduce semi joins (existential quantification)

-- | Construct a semijoin qualifier given a predicate and two generators
-- Note that the splitJoinPred call implicitly checks that only x and y
-- occur free in the predicate and no further correlation takes place.
mksemijoinT :: Expr -> Ident -> Ident -> Expr -> Expr -> TranslateC (NL Qual) Qual
mksemijoinT pred x y xs ys = do
    (leftExpr, rightExpr) <- constT (return pred) >>> splitJoinPredT x y

    let xst = typeOf xs
        yst = typeOf ys
        jt  = xst .-> yst .-> xst

    -- => [ ... | ..., x <- xs semijoin(p1, p2) ys, ... ]
    return $ BindQ x (AppE2 xst (Prim2 (SemiJoin leftExpr rightExpr) jt) xs ys)

-- | Match a IN semijoin pattern in the middle of a qualifier list
elemR :: RewriteC (NL Qual)
elemR = do
    -- [ ... | ..., x <- xs, or [ p | y <- ys ], ... ]
    BindQ x xs :* GuardQ (AppE1 _ (Prim1 Or _) (Comp _ p (S (BindQ y ys)))) :* qs <- idR
    q' <- mksemijoinT p x y xs ys
    return $ q' :* qs

-- | Match a IN semijoin pattern at the end of a list
elemEndR :: RewriteC (NL Qual)
elemEndR = do
    -- [ ... | ..., x <- xs, or [ p | y <- ys ] ]
    BindQ x xs :* (S (GuardQ (AppE1 _ (Prim1 Or _) (Comp _ p (S (BindQ y ys)))))) <- idR
    q' <- mksemijoinT p x y xs ys
    return (S q')
    
existentialQualsR :: RewriteC (NL Qual)
existentialQualsR = anytdR $ repeatR (elemR <+ elemEndR)

semijoinR :: RewriteC CL
semijoinR = do
    Comp _ _ _ <- promoteT idR
    childR 1 (promoteR existentialQualsR)

--------------------------------------------------------------------------------
-- Introduce anti joins (universal quantification)

antijoinR :: RewriteC CL
antijoinR = fail "antijoinR not implemented"

------------------------------------------------------------------
-- Pulling out expressions from comprehension heads 

type HeadExpr = Either PathC (PathC, Type, Expr, NL Qual) 

-- | Collect expressions which we would like to replace in the comprehension
-- head: occurences of the variable bound by the only generator as well as
-- comprehensions nested in the head. We collect the expressions themself as
-- well as the paths to them.
collectExprT :: Ident -> TranslateC CL [HeadExpr] 
collectExprT x = prunetdT (collectVar <+ collectComp <+ blockLambda)
  where
    -- | Collect a variable if it refers to the name we are looking for
    collectVar :: TranslateC CL [HeadExpr]
    collectVar = do
        Var _ n <- promoteT idR
        guardM $ x == n
        path <- snocPathToPath <$> absPathT
        return [Left path]
    
    -- | Collect a comprehension and don't descend into it
    collectComp :: TranslateC CL [HeadExpr]
    collectComp = do
        Comp t h qs <- promoteT idR
        -- FIXME check here if the comprehension is eligible for unnesting?
        path <- snocPathToPath <$> absPathT
        return [Right (path, t, h, qs)]
        
    -- | don't descend past lambdas which shadow the name we are looking for
    blockLambda :: TranslateC CL [HeadExpr]
    blockLambda = do
        Lam _ n _ <- promoteT idR
        guardM $ n == x
        return []
        
-- | Apply a function n times
ntimes :: Int -> (a -> a) -> a -> a
ntimes 0 _ x = x
ntimes n f x = ntimes (n - 1) f (f x)

-- | Tuple accessor for position pos in left-deep tuples
tupleAt :: Expr -> Int -> Int -> Expr
tupleAt expr len pos = 
  case pos of
      pos | pos == 1               -> ntimes (len - 1) P.fst expr
      pos | 2 <= pos && pos <= len -> P.snd $ ntimes (len - pos) P.fst expr
      _                            -> $impossible                         
        
-- | Take an absolute path and drop the prefix of the path to a direct child of
-- the current node. This makes it a relative path starting from **some** direct
-- child of the current node.
dropPrefix :: Eq a => [a] -> [a] -> [a]
dropPrefix prefix xs = drop (1 + length prefix) xs

-- | Construct a left-deep tuple from at least two expressions
mkTuple :: Expr -> NonEmpty Expr -> Expr
mkTuple e1 es = F.foldl1 P.pair (e1 <| es)

constExprT :: Monad m => Expr -> Translate c m CL CL
constExprT expr = constT $ return $ inject expr
        
-- | Factor out expressions from a single-generator comprehension head, such
-- that only (pairs of) the generator variable and nested comprehensions in the
-- head remain. Beware: This rewrite /must/ be combined with a rewrite that
-- makes progress on the comprehension. Otherwise, a loop might occur when used
-- in a top-down fashion.
factoroutHeadR :: RewriteC CL
factoroutHeadR = do factoroutEndR <+ factoroutR
  where 
    factoroutEndR :: RewriteC CL
    factoroutEndR = do
        curr@(Comp t h (S (BindQ x xs))) <- promoteT idR
        debugUnit "factoroutEndR at" curr
        mkheadmapR curr t h x xs []
        
    factoroutR :: RewriteC CL
    factoroutR = do
        curr@(Comp t h ((BindQ x xs) :* qs)) <- promoteT idR

        -- Currently, we only allow additional guards, not qualifiers.
        -- FIXME this might be extendable to additional qualifiers
        guardM $ all isGuard (toList qs)
        debugUnit "factoroutR at" curr

        mkheadmapR curr t h x xs (toList qs)

mkheadmapR 
  :: Expr          -- ^ The current comprehension
  -> Type          -- ^ Type of the current comprehension
  -> Expr          -- ^ Comprehension head
  -> Ident         -- ^ Variable bound by the generator
  -> Expr          -- ^ Generator source
  -> [Qual]        -- ^ Possible additional guards
  -> RewriteC CL
mkheadmapR curr t h x xs qs = do


    -- Collect interesting expressions from the comprehension head 
    (vars, comps) <- partitionEithers <$> (oneT $ collectExprT x)

    -- We abort if we did not find any interesting comprehensions in the head
    guardM $ not $ null comps
    
    debugUnit "mkheadmapR found" (vars, comps)

    pathPrefix <- rootPathT

    let varTy = elemT $ typeOf xs

        varExpr   = if null vars 
                    then [] 
                    else [(Var varTy x, map (dropPrefix pathPrefix) vars)]

        compExprs = map (\(p, t', h', qs) -> (Comp t' h' qs, [dropPrefix pathPrefix p])) comps
        
        exprs     = varExpr ++ compExprs
        
    -- trace ("collected: " ++ show (varExpr ++ compExprs)) $ return ()
    -- trace ("currently at: " ++ show curr ++ " --- " ++ show pathPrefix) $ return ()
        
    (mapBody, h', headTy) <- case exprs of
              -- If there is only one interesting expression (which must be a
              -- comprehension), we don't need to construct tuples.
              [(comp@(Comp _ _ _), [path])] -> do
                  let lamVarTy = typeOf comp

                  -- Replace the comprehension with the lambda variable
                  mapBody <- (oneT $ pathR path (constT $ return $ inject $ Var lamVarTy x)) >>> projectT

                  return (mapBody, comp, lamVarTy)

              -- If there are multiple expressions, we construct a left-deep tuple
              -- and replace the original expressions in the head with the appropriate
              -- tuple constructors.
              es@(e1 : e2 : er)    -> do
                  let -- Construct a tuple from all interesting expressions
                      headTuple      = mkTuple (fst e1) (fmap fst $ e2 :| er)

                      lamVarTy       = typeOf headTuple
                      lamVar         = Var lamVarTy x
                      
                      -- Map all paths to a tuple accessor for the tuple we
                      -- constructed for the comprehension head
                      tupleAccessors = zipWith (\paths i -> (tupleAt lamVar (length es) i, paths))
                                               (map snd es)
                                               [1..]
                                               
                      
                      -- For each path, construct a rewrite to replace the
                      -- original expression at this path with the tuple
                      -- accessor
                      rewritePerPath = [ pathR path (constExprT ta) 
                                       | (ta, paths) <- tupleAccessors
                                       , path <- paths ]
                                       
                  mapBody <- (oneT $ serialise rewritePerPath) >>> projectT
                  return (mapBody, headTuple, lamVarTy)

              _            -> $impossible
              
    let qs' = case fromList qs of
                  Just qsTail -> (BindQ x xs) :* qsTail
                  Nothing     -> S (BindQ x xs)
              
    let lamTy = headTy .-> (elemT t)
    return $ inject $ P.map (Lam lamTy x mapBody) (Comp (listT headTy) h' qs')

------------------------------------------------------------------
-- Nestjoin introduction: unnesting in a comprehension head
    
-- FIXME this should work on left-deep tuples
tupleComponentsT :: TranslateC CL (NonEmpty Expr)
tupleComponentsT = do
    AppE2 _ (Prim2 Pair _) _ _ <- promoteT idR
    N.reverse <$> descendT
    
  where
    descendT :: TranslateC CL (NonEmpty Expr)
    descendT = descendPairT <+ singleT
    
    descendPairT :: TranslateC CL (NonEmpty Expr)
    descendPairT = do
        AppE2 _ (Prim2 Pair _) _ e <- promoteT idR
        tl <- childT 0 descendT
        return $ e <| tl
        
    singleT :: TranslateC CL (NonEmpty Expr)
    singleT = (:| []) <$> (promoteT idR)

    
-- | Base case for nestjoin introduction: consider comprehensions in which only
-- a single inner comprehension occurs in the head.
unnestHeadBaseT :: TranslateC CL Expr
unnestHeadBaseT = singleCompEndT <+ singleCompT <+ varCompPairT <+ varCompPairEndT
  where
    mknestjoinT 
      :: Type    -- ^ Type of the outer comprehension
      -> Type    -- ^ Type of the inner comprehension
      -> Expr    -- ^ Head of the inner comprehension
      -> Ident   -- ^ Variable for the inner generator
      -> Expr    -- ^ Source for the inner generator
      -> Expr    -- ^ Inner predicate
      -> Ident   -- ^ Outer generator variable
      -> Expr    -- ^ Outer generator source
      -> [Qual]  -- ^ Possibly additional outer qualifiers
      -> TranslateC CL Expr
    mknestjoinT t1 t2 h y ys p x xs preds = do
        -- Split the join predicate
        (leftExpr, rightExpr) <- constT (return p) >>> splitJoinPredT x y
        
        let xt       = elemT $ typeOf xs
            yt       = elemT $ typeOf ys
            tupType  = pairT xt (listT yt)
            joinType = listT xt .-> (listT yt .-> listT tupType)
            joinVar  = Var tupType x
            
        -- In the head of the inner comprehension, replace x with (snd x)
        h' <- constT (return h) >>> (extractR $ tryR $ substR x (P.fst joinVar))

        -- the nestjoin operator combining xs and ys: 
        -- xs nj(p) ys
        let xs'        = AppE2 (listT tupType) (Prim2 (NestJoin leftExpr rightExpr) joinType) xs ys

            headComp = case h of
                -- The simple case: the inner comprehension looked like [ y | y < ys, p ]
                -- => We can remove the inner comprehension entirely
                Var _ y' | y == y' -> P.snd joinVar
                
                -- The complex case: the inner comprehension has a non-idenity
                -- head: 
                -- [ h | y <- ys, p ] => [ h[fst x/x] | y <- snd x ] 
                -- It is safe to re-use y here, because we just re-bind the generator.
                _               -> Comp t2 h' (S $ BindQ y (P.snd joinVar))

        preds' <- constT (return $ map inject preds) 
                  >>> mapT (tryR $ substR x (P.fst joinVar))
                  >>> mapT projectT

        let qs = case fromList preds' of
                     Just npreds -> (BindQ x xs') :* npreds
                     Nothing     -> S (BindQ x xs')
                
        return $ Comp t1 headComp qs

    -- The base case: a single comprehension nested in the head of the outer
    -- comprehension. Assume only a single outer qualifier here.
    -- [ [ h y | y <- ys, p ] | x <- xs ]
    singleCompEndT :: TranslateC CL Expr
    singleCompEndT = do
        q@(Comp _ _ _) <- promoteT idR
        debugUnit "singleCompEndT at" (q :: Expr)

        -- [ [ h | y <- ys, p ] | x <- xs ]
        q@(Comp t1 (Comp t2 h ((BindQ y ys) :* (S (GuardQ p)))) (S (BindQ x xs))) <- promoteT idR
        debug "trigger singleCompEndT" q $ mknestjoinT t1 t2 h y ys p x xs []
        
    -- The base case: a single comprehension nested in the head of the outer
    -- comprehension. Assume more than one outer qualifier here. However, we
    -- are conservative and expect only predicates as additional qualifiers
    -- here. This could propably be extended to more generators, as long as
    -- those generators do not bind variables which occur free in the inner
    -- comprehension.
    -- [ [ h y | y <- ys, p ] | x <- xs ]
    singleCompT :: TranslateC CL Expr
    singleCompT = do
    
        q@(Comp _ _ _) <- promoteT idR
        debug "singleCompT at" (q :: Expr) (return ())

        -- [ [ h | y <- ys, p ] | x <- xs, qs ]
        Comp t1 (Comp t2 h ((BindQ y ys) :* (S (GuardQ p)))) ((BindQ x xs) :* qs) <- promoteT idR
        
        guardM $ all isGuard $ toList qs
        
        mknestjoinT t1 t2 h y ys p x xs (toList qs)

    -- The head of the outer comprehension consists of a pair of generator
    -- variable and inner comprehension
    -- [ (x, [ h y | y <- ys, p ]) | x <- xs ]
    varCompPairEndT :: TranslateC CL Expr
    varCompPairEndT = do
        Comp _ (AppE2 _ (Prim2 Pair _) (Var _ x) _) (S (BindQ x' _)) <- promoteT idR

        guardM $ x == x'
        
        -- Reduce to the base case, then unnest, then patch the variable back in
        (removeVarR <+ removeVarEndR) >>> injectT >>> (singleCompEndT <+ singleCompT) >>> arr (patchVar x)

    varCompPairT :: TranslateC CL Expr
    varCompPairT = do
        Comp _ (AppE2 _ (Prim2 Pair _) (Var _ x) _) ((BindQ x' _) :* qs) <- promoteT idR
        
        guardM $ x == x'

        -- Only allow guards as additional qualifiers
        guardM $ all isGuard (toList qs)

        -- Reduce to the base case, then unnest, then patch the variable back in
        (removeVarR <+ removeVarEndR) >>> injectT >>> (singleCompEndT <+ singleCompT) >>> arr (patchVar x)
        
    -- Support rewrite: remove the variable from the outer comprehension head
    -- [ (x, [ h y | y <- ys, p ]) | x <- xs ]
    -- => [ [ h y | y <- ys, p ] | x <- xs ]
    removeVarEndR :: TranslateC CL Expr
    removeVarEndR = do
        Comp _ (AppE2 t (Prim2 Pair _) (Var _ x) comp) (S (BindQ x' xs)) <- promoteT idR
        guardM $ x == x'
        let t' = listT $ sndT t
        return $ Comp t' comp (S (BindQ x xs))

    -- Support rewrite: remove the variable from the outer comprehension head
    -- [ (x, [ h y | y <- ys, p ]) | x <- xs ]
    -- => [ [ h y | y <- ys, p ] | x <- xs ]
    removeVarR :: TranslateC CL Expr
    removeVarR = do
        Comp _ (AppE2 t (Prim2 Pair _) (Var _ x) comp) ((BindQ x' xs) :* qs) <- promoteT idR

        guardM $ x == x'

        -- Only allow guards as additional qualifiers
        guardM $ all isGuard (toList qs)

        let t' = listT $ sndT t
        return $ Comp t' comp ((BindQ x xs) :* qs)

patchVar :: Ident -> Expr -> Expr
patchVar x c =
    case c of
        Comp _ e qs@(S (BindQ x' je)) | x == x'    -> patch e x' je qs
        Comp _ e qs@((BindQ x' je) :* _) | x == x' -> patch e x' je qs
        _                                          -> $impossible
        
  where 
    patch :: Expr -> Ident -> Expr -> (NL Qual) -> Expr
    patch e x' je qs =
        let joinBindType = elemT $ typeOf je
            e'           = P.pair (P.fst (Var joinBindType x)) e
            resultType   = listT $ pairT (fstT joinBindType) (typeOf e)
        in Comp resultType e' qs

unnestHeadR :: RewriteC CL
unnestHeadR = simpleHeadR <+ tupleHeadR

  where 
    simpleHeadR :: RewriteC CL
    simpleHeadR = do
        unnestHeadBaseT >>> injectT

    tupleHeadR :: RewriteC CL
    tupleHeadR = do
        e <- promoteT idR
        debugUnit "tupleHeadR at" (e :: Expr)
        c@(Comp _ h qs) <- promoteT idR
  
        headExprs <- oneT tupleComponentsT 
        debugUnit "tupleHeadR collected" headExprs
        
        let mkSingleComp :: Expr -> Expr
            mkSingleComp expr = Comp (listT $ typeOf expr) expr qs
            
            headExprs' = case headExprs of
                v@(Var _ _) :| (comp : comps) -> P.pair v comp :| comps
                comps                         -> comps
                
            singleComps = fmap mkSingleComp headExprs'
            
        debugUnit "tupleheadR singleComps" singleComps
            
        -- FIXME fail if all translates failed -> define alternative to mapT
        unnestedComps <- constT (return singleComps) >>> mapT (injectT >>> unnestHeadBaseT)
        
        return $ inject $ F.foldl1 P.zip unnestedComps
        
nestjoinR :: RewriteC CL
nestjoinR = do
    c@(Comp _ _ _) <- promoteT idR
    debugUnit "nestjoinR at" c
    unnestHeadR <+ (factoroutHeadR >>> childR 1 unnestHeadR)

--------------------------------------------------------------------------------
-- Nestjoin introduction: unnesting comprehensions from complex predicates

nestjoinGuardR :: RewriteC CL
nestjoinGuardR = do
    c@(Comp t h qs)         <- promoteT idR 
    debugUnit "nestjoinGuardR at" c
    (tuplifyHeadR, qs') <- statefulT idR 
                           $ childT 1 (anytdR (promoteR (qualsEndR <+ qualsR)) 
                                       >>> projectT)
                                       
    h'                  <- childT 0 tuplifyHeadR >>> projectT
    return $ inject $ Comp t h' qs'
    
  where
  
    unnestGuardT :: Ident -> Expr -> TranslateC Expr (RewriteC CL, Expr, Expr)
    unnestGuardT x xs = do
    
        e <- idR
        debugUnit "unnestGuard at" (e :: Expr)
        -- FIXME passing x is not necessary since we are not interested in
        -- collecting variables.
        -- Collect exactly one comprehension from the predicate.
        (_, [(path, t, f, qs)]) <- partitionEithers <$> extractT (collectExprT x)
        debugUnit "unnestGuardT collected" (path, t, f, qs)
        
        -- Check the shape of the inner qualifier list
        BindQ y ys :* (S (GuardQ q))  <- return qs
        
        -- Do we have a join predicate?
        (leftExpr, rightExpr)         <- constT (return q) >>> splitJoinPredT x y
        
        let xt       = elemT $ typeOf xs
            yt       = elemT $ typeOf ys
            tupType  = pairT xt (listT yt)
            joinType = listT xt .-> (listT yt .-> listT tupType)
            joinVar  = Var tupType x
            
            -- The nestjoin combining xs and ys
            xs'      = AppE2 (listT tupType) (Prim2 (NestJoin leftExpr rightExpr) joinType) 
                             xs 
                             ys
            
            tuplifyHeadR = substR x (P.fst joinVar)
            
        pathPrefix <- rootPathT
        let relPath = dropPrefix pathPrefix path
        
        debugUnit "pathPrefix, path, relPath" (pathPrefix, path, relPath)

        -- Substitute the body of the guard comprehension. As x might not occur,
        -- we need to guard the call.
        f' <- tryR $ constT (return $ inject f) >>> tuplifyHeadR >>> projectT
        
        debugUnit "f'" f'

        let c = Comp t f' (S (BindQ y (P.snd joinVar)))
        
        -- p[fst x/x][c/e'] 

        -- FIXME this looks a bit fragile. Actually, the tuplify substitution
        -- should not kill the path to the comprehension, but it would be better
        -- to be sure about this.
        p' <- injectT
              >>> tuplifyHeadR 
              >>> anyR (pathR relPath (constT (return $ inject c))) 
              >>> projectT
              
        debugUnit "p'" p'
        
        return (tuplifyHeadR, xs', p')
        
    qualsEndR :: Rewrite CompCtx TuplifyM (NL Qual)
    qualsEndR = do
        c@(BindQ x xs :* (S (GuardQ p))) <- idR
        debugUnit "qualsEndR at" c
        (tuplifyHeadR, xs', p') <- liftstateT $ constT (return p) >>> unnestGuardT x xs
        debugUnit "qualsEndR (1)" xs'
        constT $ modify (>>> tuplifyHeadR)
        return $ BindQ x xs' :* (S (GuardQ p'))

    qualsR :: Rewrite CompCtx TuplifyM (NL Qual)
    qualsR = do
        BindQ x xs :* GuardQ p :* qs <- idR
        (tuplifyHeadR, xs', p') <- liftstateT $ constT (return p) >>> unnestGuardT x xs
        constT $ modify (>>> tuplifyHeadR)
        qs' <- liftstateT $ constT (return $ inject qs) >>> tuplifyHeadR >>> projectT
        return $ BindQ x xs' :* GuardQ p' :* qs'
        
    
--------------------------------------------------------------------------------
-- Filter pushdown

selectR :: RewriteC (NL Qual)
selectR = pushR <+ pushEndR
  where
    pushR :: RewriteC (NL Qual)
    pushR = do
        (BindQ x xs) :* GuardQ p :* qs <- idR
        
        -- We only push predicates into generators if the predicate depends
        -- solely on this generator
        let fvs = freeVars p
        guardM $ [x] == fvs
        
        return $ BindQ x (P.filter (Lam ((elemT $ typeOf xs) .-> boolT) x p) xs) :* qs
        
        
    pushEndR :: RewriteC (NL Qual)
    pushEndR = do
        (BindQ x xs) :* (S (GuardQ p)) <- idR
        
        -- We only push predicates into generators if the predicate depends
        -- solely on this generator
        let fvs = freeVars p
        guardM $ [x] == fvs
        
        return $ S $ BindQ x (P.filter (Lam ((elemT $ typeOf xs) .-> boolT) x p) xs)

------------------------------------------------------------------
-- Simple housecleaning support rewrites.
    
-- | Eliminate a map with an identity body
-- map (\x -> x) xs => xs
identityMapR :: RewriteC Expr
identityMapR = do
    AppE2 _ (Prim2 Map _) (Lam _ x (Var _ x')) xs <- idR
    guardM $ x == x'
    return xs
    
-- | Eliminate a comprehension with an identity head
-- [ x | x <- xs ] => xs
identityCompR :: RewriteC Expr
identityCompR = do
    Comp _ (Var _ x) (S (BindQ x' xs)) <- idR
    guardM $ x == x'
    return xs
    
-- | Eliminate tuple construction if the elements are first and second of the
-- same tuple:
-- pair (fst x) (snd x) => x
pairR :: RewriteC Expr
pairR = do
    AppE2 _ (Prim2 Pair _) (AppE1 _ (Prim1 Fst _) v@(Var _ x)) (AppE1 _ (Prim1 Snd _) (Var _ x')) <- idR
    guardM $ x == x'
    return v
    
mergeFilterR :: RewriteC Expr
mergeFilterR = do
    AppE2 t (Prim2 Filter _) 
            (Lam t1 x1 p1)
            (AppE2 _ (Prim2 Filter _)
                     (Lam t2 x2 p2)
                     xs)                <- idR

    let xt = elemT $ typeOf xs
                     
    p2' <- (constT $ return $ inject p2) >>> substR x2 (Var xt x1) >>> projectT
    
    let p' = BinOp (xt .-> boolT) Conj p1 p2'
    
    return $ P.filter (Lam (xt .-> boolT) x1 p') xs

cleanupR :: RewriteC CL
cleanupR = anytdR $ promoteR (identityMapR <+ identityCompR <+ pairR <+ mergeFilterR)
    
------------------------------------------------------------------
-- Simple normalization rewrites

-- | Split conjunctive predicates.
splitConjunctsR :: RewriteC (NL Qual)
splitConjunctsR = splitR <+ splitEndR
  where
    splitR :: RewriteC (NL Qual)
    splitR = do
        (GuardQ (BinOp _ Conj p1 p2)) :* qs <- idR
        return $ GuardQ p1 :* GuardQ p2 :* qs
    
    splitEndR :: RewriteC (NL Qual)
    splitEndR = do
        (S (GuardQ (BinOp _ Conj p1 p2))) <- idR
        return $ GuardQ p1 :* (S $ GuardQ p2)
    
-- | Normalize a guard expressing existential quantification:
-- not $ null [ ... | x <- xs, p ] (not $ length [ ... ] == 0)
-- => or [ p | x <- xs ]
normalizeExistentialR :: RewriteC Qual
normalizeExistentialR = do
    GuardQ (AppE1 _ (Prim1 Not _) 
               (BinOp _ Eq 
                   (AppE1 _ (Prim1 Length _) 
                       (Comp _ _ (BindQ x xs :* (S (GuardQ p)))))
                   (Lit _ (IntV 0)))) <- idR

    return $ GuardQ (P.or (Comp (listT boolT) p (S (BindQ x xs))))

-- | Normalize a guard expressing universal quantification:
-- null [ ... | x <- xs, p ] (length [ ... ] == 0)
-- => and [ not p | x <- xs ]
normalizeUniversalR :: RewriteC Qual
normalizeUniversalR = do
    GuardQ (BinOp _ Eq 
                (AppE1 _ (Prim1 Length _) 
                    (Comp _ _ (BindQ x xs :* (S (GuardQ p)))))
                (Lit _ (IntV 0))) <- idR

    return $ GuardQ (P.and (Comp (listT boolT) (P.not p) (S (BindQ x xs))))
    
normalizeR :: RewriteC CL
normalizeR = repeatR $ anytdR $ promoteR splitConjunctsR
                                <+ promoteR normalizeExistentialR
                                <+ promoteR normalizeUniversalR
           

------------------------------------------------------------------
-- Monad Comprehension Normalization rules
   
-- M-Norm-1: Eliminate comprehensions with empty generators
m_norm_1R :: RewriteC CL
m_norm_1R = do
    Comp t _ _ <- promoteT idR
    matches <- childT 1 $ onetdT (promoteT $ patternT <+ patternEndT)
    guardM matches
    return $ inject $ Lit t (ListV [])
    
  where 
    patternT :: TranslateC (NL Qual) Bool
    patternT = do
        BindQ _ (Lit _ (ListV [])) :* _ <- idR
        return True
        
    patternEndT :: TranslateC (NL Qual) Bool
    patternEndT = do
        (S (BindQ _ (Lit _ (ListV [])))) <- idR
        return True

-- M-Norm-2: eliminate singleton generators.
-- [ h | qs, x <- [v], qs' ]
-- => [ h[v/x] | qs, qs'[v/x] ]
m_norm_2R :: RewriteC CL
m_norm_2R = singletonCompR <+ compR
    
  where
    -- This rewrite is a bit annoying: If it triggers, we can remove a
    -- qualifier. However, the type NL forces us to take care that we do not
    -- produce a comprehension with an empty qualifier list.
    
    -- Due to non-empty NL lists, we have to consider the case of
    -- removing a (the!) qualifier from a singleton list.
    singletonCompR :: RewriteC CL
    singletonCompR = do
        Comp t h (S q) <- promoteT idR
        (x, e) <- constT (return q) >>> qualT
        constT (return $ inject h) >>> substR x e
    
    -- The main rewrite
    compR :: RewriteC CL
    compR = do
        Comp t h (_ :* _)   <- promoteT idR
        (tuplifyHeadR, qs') <- statefulT idR $ childT 1 (anytdR (promoteR (qualsEndR <+ qualsR)) >>> projectT)
        h'                  <- childT 0 tuplifyHeadR >>> projectT
        return $ inject $ Comp t h' qs'

    -- Match the pattern (singleton generator) on a qualifier
    qualT :: TranslateC Qual (Ident, Expr)
    qualT = do
        q <- idR
        case q of
            -- x <- [v]
            BindQ x e@(Lit t (ListV [v]))                 -> return (x, Lit (elemT t) v)
            -- x <- v : []
            BindQ x e@(BinOp _ Cons v (Lit _ (ListV []))) -> return (x, v)
            _                                             -> fail "qualR: no match"
            
    -- Try to match the pattern at the end of the qualifier list
    qualsEndR :: Rewrite CompCtx TuplifyM (NL Qual)
    qualsEndR = do
        q1 :* (S q2) <- idR
        (x, e)       <- liftstateT $ constT (return q2) >>> qualT
        constT $ modify (>>> substR x e)
        return (S q1)
        
    -- Try to match the pattern in the middle of the qualifier list
    qualsR :: Rewrite CompCtx TuplifyM (NL Qual)
    qualsR = do
        q1 :* q2 :* qs <- idR
        (x, e)         <- liftstateT $ constT (return q2) >>> qualT
        qs' <- liftstateT $ constT (return $ inject qs) >>> substR x e >>> projectT
        constT $ modify (>>> substR x e)
        return $ q1 :* qs' 
        
-- M-Norm-3: unnest comprehensions from a generator
-- [ h | qs, x <- [ h' | qs'' ], qs' ]
-- => [ h[h'/x] | qs, qs'', qs'[h'/x] ]
m_norm_3R :: RewriteC CL
m_norm_3R = do
    Comp t h qs <- promoteT idR
    (tuplifyHeadR, qs') <- statefulT idR $ childT 1 (anytdR (promoteR (qualsEndR <+ qualsR)) >>> projectT)
    h'                  <- childT 0 tuplifyHeadR >>> projectT
    return $ inject $ Comp t h' qs'
    
  where
  
    qualT :: TranslateC Qual (Ident, Expr, NL Qual)
    qualT = do
        BindQ x (Comp _ h' qs'') <- idR
        return (x, h', qs'')
       
    qualsEndR :: Rewrite CompCtx TuplifyM (NL Qual)
    qualsEndR = do
        (S q) <- idR
        (x, h', qs'') <- liftstateT $ (constT $ return q) >>> qualT
        constT $ modify (>>> substR x h')
        return qs''
        
    qualsR :: Rewrite CompCtx TuplifyM (NL Qual)
    qualsR = do
        q :* qs <- idR
        (x, h', qs'') <- liftstateT $ (constT $ return q) >>> qualT
        qs' <- liftstateT $ constT (return $ inject qs) >>> substR x h' >>> projectT
        constT $ modify (>>> substR x h')
        return $ appendNL qs'' qs'
     


{- 
m_norm_2 :: RewriteC CL
m_norm_2 = do
    Comp _ _ _ <- promoteT idR
    (absPath, x, e) <- childT 1 $ onetdSpineT (promoteT patternT)
    let clPath = undefined
    
    h' <- childR 1 $ substR x e
    
    let qualsR :: RewriteC (NL Qual)
        qualsR = do
            _ :* qs <- idR
            consT (return qs) >>> (tryR $ subst x e)
        
        -- If we encounter a match on the last qualifier, we have to turn the
        -- next-to-last qualifier into a singleton
        lastR :: RewriteC (NL Qual)
        lastR = do
            case init clPath of
                c : cs -> undefined
                []     -> undefined
            undefined
              
    pathR childR

  where
    patternT :: TranslateC Qual (PathC, Ident, Expr)
    patternT = do
        q <- idR
        case q of
            -- x <- [v]
            BindQ x e@(Lit _ (ListV [v]))                 -> do
                -- return the path to the parent node, i.e. the NL node
                p <- init <$> rootPathT
                return (p, x, e)
            -- x <- v : []
            BindQ x e@(BinOp _ Cons v (Lit _ (ListV []))) -> do
                -- return the path to the parent node, i.e. the NL node
                p <- init <$> rootPathT
                return (p, x, e)
  
-}

--------------------------------------------------------------------------------
-- Partial evaluation rules

fstR :: RewriteC Expr
fstR = do
    AppE1 _ (Prim1 Fst _) (AppE2 _ (Prim2 Pair _) e1 _) <- idR
    return e1

sndR :: RewriteC Expr
sndR = do
    AppE1 _ (Prim1 Snd _) (AppE2 _ (Prim2 Pair _) _ e2) <- idR
    return e2

--------------------------------------------------------------------------------
-- Rewrite Strategy
        
test2 :: RewriteC CL
-- test2 = (semijoinR <+ nestjoinR) >>> repeatR (anytdR (promoteR cleanupR))
-- test2 = semijoinR
-- test2 = anytdR (promoteR $ splitConjunctsR <+ splitConjunctsEndR)
-- test2 = anytdR eqjoinCompR
test2 = anytdR $ promoteR normalizeExistentialR
        
strategy :: RewriteC CL
-- strategy = {- anybuR (promoteR pushEquiFilters) >>> -} anytdR eqjoinCompR
-- strategy = repeatR (anybuR normalizeR)
-- strategy = repeatR (anytdR $ promoteR selectR >+> promoteR cleanupR)

compStrategy :: RewriteC Expr
compStrategy = do
    -- Don't try anything on a non-comprehension
    Comp _ _ _ <- idR 

    repeatR $ (extractR (tryR cleanupR) >>> tryR pushSemiFilters >>> extractR semijoinR)
              >+> (extractR (tryR cleanupR) >>> tryR pushAntiFilters >>> extractR antijoinR)
              >+> (extractR (tryR cleanupR) >>> tryR pushEquiFilters >>> extractR eqjoinCompR)

strategy = -- First, 
           (anytdR $ promoteR normalizeR) 
           >+> (repeatR $ anytdR $ promoteR compStrategy)
           >+> (repeatR $ anybuR $ (promoteR (tryR cleanupR)) >>> nestjoinR)
           
test :: RewriteC CL
test = nestjoinGuardR
           
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
        "\nOriginal query ===================================================================\n"
        ++ show e 
        ++ "\n=================================================================================="
        
    showOpt :: Expr -> String
    showOpt e =
        "Optimized query ===================================================================\n"
        ++ show e 
        ++ "\n=================================================================================="
        
           
opt :: Expr -> Expr
opt expr = debugOpt expr optimizedExpr

  where
    -- optimizedExpr = applyExpr (strategy >>> projectT) expr
    optimizedExpr = applyExpr (test >>> projectT) expr
