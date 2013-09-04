{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE TemplateHaskell     #-}
    
-- | This module performs optimizations on the Comprehension Language (CL).
module Database.DSH.CL.Opt 
  ( opt ) where
       
import           Debug.Trace
                 
import           Control.Applicative((<$>), (<*>))
import           Control.Arrow
import qualified Control.Category as C
-- import           Control.Monad

import           Data.Either

import qualified Data.Foldable as F

import Data.List.NonEmpty(NonEmpty((:|)))
-- import qualified Data.List.NonEmpty as N

-- import qualified Data.Set as S
-- import           GHC.Exts

import           Language.KURE.Lens
                 
import           Database.DSH.Impossible

-- import           Database.DSH.Impossible

import           Database.DSH.CL.Lang
import           Database.DSH.CL.Kure
import           Database.DSH.CL.OptUtils

import qualified Database.DSH.CL.Primitives as P

--------------------------------------------------------------------------------
-- Pushing filters towards the front of a qualifier list

pushFilters :: (Expr -> Bool) -> RewriteC Expr
pushFilters mayPush = pushFiltersOnComp
  where
    pushFiltersOnComp :: RewriteC Expr
    pushFiltersOnComp = do
        Comp _ _ _ <- idR
        compR idR pushFiltersQuals
        
    pushFiltersQuals :: RewriteC (NL Qual)
    pushFiltersQuals = (reverseNL . fmap initFlags)
                       -- FIXME using innermostR here is really inefficient!
                       ^>> innermostR tryPush 
                       >>^ (reverseNL . fmap snd)
                       
    tryPush :: RewriteC (NL (Bool, Qual))
    tryPush = do
        qualifiers <- idR 
        trace (show qualifiers) $ case qualifiers of
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
    
    initFlags :: Qual -> (Bool, Qual)
    initFlags q@(GuardQ p)  = (mayPush p, q)
    initFlags q@(BindQ _ _) = (False, q)

pushEquiFilters :: RewriteC Expr
pushEquiFilters = pushFilters isEquiJoinPred
       
isEquiJoinPred :: Expr -> Bool
isEquiJoinPred (BinOp _ Eq e1 e2) = isProj e1 && isProj e2
isEquiJoinPred _                  = False

isProj :: Expr -> Bool
isProj (AppE1 _ (Prim1 Fst _) e) = isProj e
isProj (AppE1 _ (Prim1 Snd _) e) = isProj e
isProj (AppE1 _ (Prim1 Not _) e) = isProj e
isProj (BinOp _ _ e1 e2)         = isProj e1 && isProj e2
isProj (Var _ _)                 = True
isProj _                         = False

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
splitJoinPred :: Ident -> Ident -> TranslateC Expr (JoinExpr, JoinExpr)
splitJoinPred x y = do
    BinOp _ Eq e1 e2 <- idR

    let fv1 = freeVars e1
        fv2 = freeVars e2
        
    if [x] == fv1 && [y] == fv2
        then binopT (toJoinExpr x) (toJoinExpr y) (\_ _ e1' e2' -> (e1', e2'))
        else if [y] == fv1 && [x] == fv2
             then binopT (toJoinExpr x) (toJoinExpr y) (\_ _ e1' e2' -> (e2', e1'))
             else fail "splitJoinPred: not an equi-join predicate"

--------------------------------------------------------------------------------
-- Introduce simple equi joins

type TuplifyM = CompSM (RewriteC CL)

eqjoinR :: Rewrite CompCtx TuplifyM (NL Qual)
eqjoinR = do
    -- We need two generators followed by a predicate
    BindQ x xs :* BindQ y ys :* GuardQ p :* qr <- promoteT idR
    
    -- Two tail steps into the list, then first the guard node and then the
    -- predicate expression 
    
    -- The predicate must be an equi join predicate
    (leftExpr, rightExpr) <- constT (return p) >>> (liftstateT $ splitJoinPred x y)

    -- Conditions for the rewrite are fulfilled. 
    let xst     = typeOf xs
        yst     = typeOf ys
        xt      = elemT xst
        yt      = elemT yst
        pt      = listT $ pairT xt yt
        jt      = xst .-> (yst .-> pt)
        tuplifyR = tuplify x (x, xt) (y, yt)
        joinGen = BindQ x 
                        (AppE2 pt 
                               (Prim2 (EquiJoin leftExpr rightExpr) jt) 
                               xs ys)
                               
    -- Next, we apply the tuplify rewrite to the tail, i.e. to all following
    -- qualifiers
    -- FIXME check if tuplify fails when no changes happen
    -- FIXME why is extractT required here?
    -- FIXME this should propably be guarded
    qr' <- liftstateT $ (constT $ return qr) >>> (extractR tuplifyR)

    -- Combine the new tuplifying rewrite with the current rewrite by chaining
    -- both rewrites
    constT $ modify (>>> tuplifyR)
    
    return $ joinGen :* qr'
    
eqjoinQualsR :: Rewrite CompCtx TuplifyM (NL Qual) 
eqjoinQualsR = anytdR $ repeatR eqjoinR
    
-- FIXME this should work without this amount of casting
-- FIXME and it should be RewriteC Expr
eqjoinCompR :: RewriteC CL
eqjoinCompR = do
    Comp t e _      <- promoteT idR
    (tuplifyR, qs') <- statefulT idR $ childT 1 (promoteR eqjoinQualsR >>> projectT)
    e'              <- (tryR $ childT 0 tuplifyR) >>> projectT
    return $ inject $ Comp t e' qs'

--------------------------------------------------------------------------------
-- Introduce semi joins (existential quantification

existentialR :: RewriteC (NL Qual)
existentialR = do
    -- [ ... | ..., x <- xs, or [ p | y <- ys ], ... ]
    BindQ x xs :* GuardQ (AppE1 _ (Prim1 Or _) (Comp _ p (S (BindQ y ys)))) :* qs <- idR

    (leftExpr, rightExpr) <- constT (return p) >>> splitJoinPred x y

    let xst = typeOf xs
        yst = typeOf ys
        jt  = xst .-> yst .-> xst

    -- => [ ... | ..., x <- xs semijoin(p1, p2) ys, ... ]
    return $ BindQ x (AppE2 xst (Prim2 (SemiJoin leftExpr rightExpr) jt) xs ys) :* qs
    
existentialQualsR :: RewriteC (NL Qual)
existentialQualsR = anytdR $ repeatR existentialR

------------------------------------------------------------------
-- Pulling out expressions from comprehension heads 

{- FIXME consider what happens if the head does not need to be normalized,
i.e. is already in the proper shape -} 

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
        Var t n <- promoteT idR
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
        Lam t n b <- promoteT idR
        guardM $ n == x
        return []

-- Tuple accessor for position pos in right-deep tuples
tupleAt :: Expr -> Int -> Int -> Expr
tupleAt expr len pos = unpackTuple len (typeOf expr) expr
  where
    unpackTuple :: Int -> Type -> Expr -> Expr
    unpackTuple l t@(PairT _ t2) e | pos == l && pos > 1 
        = AppE1 t2 (Prim1 Snd (t .-> t2)) e

    unpackTuple l t@(PairT t1 _) e | pos < l && l > 2    
        = unpackTuple (l - 1) t1 (AppE1 t1 (Prim1 Fst (t .-> t1)) e)

    unpackTuple 2 t@(PairT t1 _) e | pos == 1            
        = AppE1 t1 (Prim1 Fst (t .-> t1)) e

    unpackTuple d t e 
        = error $ "tupleAt failed " ++ show d ++ " " ++ show t ++ " " ++ show e
        
-- | Take an absolute path and drop the prefix of the path to a direct child of
-- the current node. This makes it a relative path starting from **some** direct
-- child of the current node.
dropPrefix :: Eq a => [a] -> [a] -> [a]
dropPrefix prefix xs = drop (1 + length prefix) xs

-- | Construct a right-deep tuple from at least two expressions
mkTuple :: Expr -> NonEmpty Expr -> Expr
mkTuple e1 es = P.pair e1 (F.foldr1 P.pair es)

constExprT :: Monad m => Expr -> Translate c m CL CL
constExprT expr = constT $ return $ inject expr
        
-- FIXME this should be RewriteC Expr
pulloutHeadR :: RewriteC CL
pulloutHeadR = do
    curr@(Comp t h (S (BindQ x xs))) <- promoteT idR
    (vars, comps) <- partitionEithers <$> (oneT $ collectExprT x)

    -- We abort if we did not find any interesting comprehensions in the head
    guardM $ not $ null comps

    pathPrefix <- rootPathT

    let varTy = elemT $ typeOf xs

        varExpr   = if null vars 
                    then [] 
                    else [(Var varTy x, map (dropPrefix pathPrefix) vars)]

        compExprs = map (\(p, t, h, qs) -> (Comp t h qs, [dropPrefix pathPrefix p])) comps
        
    trace ("collected: " ++ show (varExpr ++ compExprs)) $ return ()
    trace ("currently at: " ++ show curr ++ " --- " ++ show pathPrefix) $ return ()
        
    (mapBody, h', headTy) <- case varExpr ++ compExprs of
              -- If there is only one interesting expression (which must be a
              -- comprehension), we don't need to construct tuples.
              [(comp@(Comp _ _ _), [path])] -> do
                  let lamVarTy = typeOf comp

                  -- Replace the comprehension with the lambda variable
                  mapBody <- (oneT $ pathR path (constT $ return $ inject $ Var lamVarTy x)) >>> projectT

                  return (mapBody, comp, lamVarTy)

              -- If there are multiple expressions, we construct a right-deep tuple
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
        
    let lamTy = headTy .-> (elemT t)
    return $ inject $ P.map (Lam lamTy x mapBody) (Comp (listT headTy) h' (S (BindQ x xs)))
        
{-
test :: RewriteC CL
test = anytdR walk

  where
    walk :: TranslateC CL CL
    walk = do
        Comp _ h (S (BindQ x _)) <- promoteT idR
        paths <- oneT $ collectExprT x
        trace (show paths) idR
-}        
        
test2 :: RewriteC CL
test2 = pulloutHeadR
        
  
strategy :: RewriteC CL
-- strategy = {- anybuR (promoteR pushEquiFilters) >>> -} anytdR eqjoinCompR
strategy = test2

opt :: Expr -> Expr
opt expr = trace "foo" $ either (\msg -> trace msg expr) (\expr -> trace (show expr) expr) rewritten
  where
    rewritten = applyExpr (strategy >>> projectT) expr
