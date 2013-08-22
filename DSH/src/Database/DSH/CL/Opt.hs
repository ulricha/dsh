{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE QuasiQuotes      #-}
{-# LANGUAGE TemplateHaskell  #-}
    
-- | This module performs optimizations on the Comprehension Language (CL).
module Database.DSH.CL.Opt 
  ( opt ) where
       
import           Debug.Trace
import           Text.Printf
                 
import           Control.Applicative((<$>), (<*>))
import           Control.Monad
import           Control.Arrow

import qualified Data.Set as S
import           GHC.Exts

import           Database.DSH.Impossible

import           Database.DSH.CL.Lang
import           Database.DSH.CL.Kure
import           Database.DSH.CL.OptUtils

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

{-

-- | Try to transform an expression into an equijoin predicate. This will fail
-- if either the expression does not have the correct shape (equality with
-- simple projection expressions on both sides) or if one side of the predicate
-- has free variables which are not the variables of the qualifiers given to the
-- function.
splitJoinPred :: Expr -> Ident -> Ident -> Maybe (JoinExpr, JoinExpr)
splitJoinPred (BinOp _ Eq e1 e2) x y = 
    case (S.elems $ freeVars e1, S.elems $ freeVars e2) of
        ([x'], [y']) | x == x' && y == y'  -> do
            je1 <- toJoinExpr e1 x
            je2 <- toJoinExpr e2 y
            return (je1, je2)
        ([y'], [x']) | x == x' && y == y' -> do
            je1 <- toJoinExpr e2 x
            je2 <- toJoinExpr e1 y
            return (je1, je2)
        _                                 -> mzero

splitJoinPred _ _ _               = mzero
              

toJoinExpr :: Expr -> Ident -> Maybe JoinExpr
toJoinExpr (AppE1 _ (Prim1 Fst _) e) x = UnOpJ FstJ <$> toJoinExpr e x
toJoinExpr (AppE1 _ (Prim1 Snd _) e) x = UnOpJ SndJ <$> toJoinExpr e x
toJoinExpr (AppE1 _ (Prim1 Not _) e) x = UnOpJ NotJ <$> toJoinExpr e x
toJoinExpr (BinOp _ o e1 e2)         x = BinOpJ o <$> toJoinExpr e1 x 
                                                  <*> toJoinExpr e2 x
toJoinExpr (Lit _ v)               _   = return $ ConstJ v
toJoinExpr (Var _ x') x | x == x'      = return InputJ
toJoinExpr _                         _ = mzero
        
introduceEquiJoins :: Expr -> Expr
introduceEquiJoins expr = transform go expr
  where 
    go :: Expr -> Expr
    go (Comp t e (Quals qs)) = Comp t e' (Quals qs') where (e', qs') = buildJoins e qs
    go e                     = e
    
    -- We traverse the qualifier list and look for an equi join pattern:
    -- [ e | qs, x <- xs, y <- ys, p, qs' ]
    -- = [ tuplify e x y | qs, x <- eqjoin p xs ys, tuplifyQuals qs' x y ]
    buildJoins :: Expr -> [Qual] -> (Expr, [Qual])
    buildJoins e qs = let (e', qs') = traverse e qs
                      in (e', qs')

    traverse :: Expr -> [Qual] -> (Expr, [Qual])
    traverse e [] = (e, [])
    traverse e (BindQ x xs : BindQ y ys : GuardQ p : qs) =
        case splitJoinPred p x y of
            Just (leftExpr, rightExpr) ->
                let xst     = typeOf xs
                    yst     = typeOf ys
                    xt      = elemT xst
                    yt      = elemT yst
                    pt      = listT $ pairT xt yt
                    jt      = xst .-> (yst .-> pt)
                    e'      = tuplify (x, xt) (y, yt) e
                    qs'     = tuplifyQuals (x, xt) (y, yt) qs
                    joinGen = BindQ x 
                                    (AppE2 pt 
                                           (Prim2 (EquiJoin leftExpr rightExpr) jt) 
                                           xs ys)
                 in traverse e' (joinGen : qs')
              
            Nothing                    ->
                let (e', qs') = traverse e qs
                in  (e', BindQ x xs : BindQ y ys : GuardQ p : qs')
          
    traverse e (q : qs) =
        let (e', qs') = traverse e qs
        in  (e', q : qs')
         
{-
------------------------------------------------------------------
-- Pulling out expressions from comprehension heads 
  
newtype QuantVars    = Q (S.Set Ident)
newtype ShadowedVars = S (S.Set Ident)

type ProjectEnv = (QuantVars, ShadowedVars)
  
type Collect = ReaderT ProjectEnv (Writer [Expr])

bindLocally :: MonadReader ProjectEnv m => Ident -> m a -> m a
bindLocally i a = local maybeBind a
  where 
    maybeBind (Q qs, S ss) = if i `S.member` qs
                             then (Q qs, S $ S.insert i ss)
                             else (Q qs, S ss)
                           
isNotShadowed :: MonadReader ProjectEnv m => Ident -> m Bool
isNotShadowed i = do
    (Q qs, S ss) <- ask
    return $ (i `S.member` qs) && (not $ i `S.member` ss)
  
areNotShadowed :: MonadReader ProjectEnv m => S.Set Ident -> m Bool
areNotShadowed is = do
    S ss <- asks snd
    return $ S.null $ is `S.intersection` ss

-- Collect all expressions which we have to keep in the comprehension head.
collectExpressions :: Expr -> [Expr]
collectExpressions expr = execWriter $ runReaderT (collect expr) initEnv
  where
    initEnv :: ProjectEnv
    initEnv = (Q $ freeVars expr, S S.empty)

    collect :: Expr -> Collect ()
    collect (Table _ _ _ _)   = return ()
    collect (App _ e1 e2)     = collect e1 >> collect e2
    collect (AppE1 _ _ e1)    = collect e1
    collect (AppE2 _ _ e1 e2) = collect e1 >> collect e2
    collect (Lam _ x e)       = bindLocally x (collect e)
    collect (If _ e1 e2 e3)   = mapM_ collect [e1, e2, e3]
    collect (BinOp _ _ e1 e2) = collect e1 >> collect e2
    collect (Lit _ _)         = return ()
    collect v@(Var _ x)       = isNotShadowed x >>= flip when (tell [v])
    collect c@(Comp _ b qs)   = areNotShadowed (freeVars c) >>= flip when (tell [c])
    
-- Tuple accessor for position pos.
tupleAt :: Expr -> Int -> Expr
tupleAt expr pos = descend 1 (typeOf expr) expr
  where
    descend :: Int -> Type -> Expr -> Expr
    descend p t@(PairT t1 t2) e | p == pos = AppE1 t1 (Prim1 Fst (t .-> t1)) e
    descend p _               e | p == pos = e
    descend p t@(PairT t1 t2) e | p < pos  = descend (p + 1) t2 (AppE1 t2 (Prim1 Snd (t .-> t2)) e)
    descend _ _             _              = $impossible
    
-- Construct a tuple from a list of expressions. The tuple is constructed as
-- right-deep nested pairs.
constructTuple :: NonEmpty Expr -> Expr
constructTuple (e :| []) = e
constructTuple (e :| es) = foldr1 construct (e : es) 
  where
    construct :: Expr -> Expr -> Expr
    construct e tup = 
        let te = typeOf e
            tt = typeOf tup
            t  = pairT te tt
        in AppE2 t (Prim2 Pair (te .-> (tt .-> t))) e tup

-- From the list of expressions to be kept in the comprehension head, construct
-- the tuple for the head which contains all those expressions and the list of
-- tuple accessors which serve as replacements in the factored-out expression.
buildReplacements :: Ident -> [Expr] -> (Expr, [Expr])
buildReplacements tupleName exprs = (tuple, replacementExprs)

  where
    -- canonical order: variables first, then comprehensions
    canonicalOrder = uncurry (++) $ partition isComp $ zip exprs [1..]

    tuple = case map fst canonicalOrder of
                e : es -> constructTuple (e :| es)
                []     -> $impossible
    
    isComp :: (Expr, Int) -> Bool
    isComp (Comp _ _ _, _) = True
    isComp _               = False
    
    tupleVar = Var (typeOf tuple) tupleName
    
    replacementExprs = 
        -- construct tuple accessors
        map ((tupleAt tupleVar) . fst) 
        -- sort into the original expression order
        $ sortWith snd 
        -- keep the canonical order (these are the tuple indices)
        $ zip [1..] 
        $ map snd canonicalOrder
 
type Replace = ReaderT ProjectEnv (State [Expr])

-- Get the next replacement expression
getReplacement :: Replace Expr
getReplacement = do
  s <- get
  case s of
    r : rs -> put rs >> return r
    []     -> $impossible
    
-- Traverse the expression again and replace all expressions which we collected
-- during the first traversal.
replaceExpressions :: Expr -> [Expr] -> Expr
replaceExpressions expr replacements = evalState (runReaderT (replace expr) initEnv) replacements
  where
    initEnv :: ProjectEnv
    initEnv = (Q $ freeVars expr, S S.empty)
    
    replace :: Expr -> Replace Expr
    replace t@(Table _ _ _ _)   = return t

    replace (App t e1 e2)     = do
        e1' <- replace e1
        e2' <- replace e2
        return $ App t e1' e2'
      
    replace (AppE1 t p e1)    = do
        e1' <- replace e1
        return $ AppE1 t p e1'

    replace (AppE2 t p e1 e2) = do
        e1' <- replace e1
        e2' <- replace e2
        return $ AppE2 t p e1' e2'

    replace (Lam t x e)       = do
        e' <- bindLocally x (replace e)
        return $ Lam t x e'

    replace (If t e1 e2 e3)   = do
        e1' <- replace e1
        e2' <- replace e2
        e3' <- replace e3
        return $ If t e1' e2' e3'

    replace (BinOp t o e1 e2) = do
        e1' <- replace e1
        e2' <- replace e2
        return $ BinOp t o e1' e2'

    replace c@(Lit _ _)       = return c

    replace v@(Var _ x)       = do 
        interesting <- isNotShadowed x
        if interesting
            then getReplacement
            else return v

    replace c@(Comp _ b qs)   = do
        interesting <- areNotShadowed (freeVars c)
        if interesting
            then getReplacement
            else return c

comprehensionHead :: Expr -> Expr
comprehensionHead expr = transform go expr
  where
    go :: Expr -> Expr
    go (Comp t e qs) = project undefined e qs
    go e             = e
    
    project :: Type -> Expr -> [Qual] -> Expr
    project _ _ _  = undefined
    project t e qs = Comp t e qs
-}
    
-- Try to unnest comprehensions from a comprehension's head using the nestjoin
-- operator. Currently, we can only deal with a rather limited pattern (see
-- below). However, this should be generalizable to multiple nested
-- comprehensions and complicated head expressions by normalizing the
-- comprehension head.
unnestComprehensionHead :: Expr -> Expr
unnestComprehensionHead expr = transform go expr
  where
    go :: Expr -> Expr
    go (Comp t e (Quals qs)) = Comp t e' (Quals qs') where (e', qs') = unnestHead e qs
    go e                     = e
    
    quantifierBindings :: [Qual] -> [Ident]
    quantifierBindings qs = mapMaybe aux qs
      where
        aux (BindQ i _) = Just i
        aux (GuardQ _)  = Nothing
    
    unnestHead :: Expr -> [Qual] -> (Expr, [Qual])
    -- [ (x, [ g y | y <- ys, p x y ]) | x <- xs ]
    -- => [ (fst x, map (\y -> g y) snd x) | x <- xs nj(p) ys ]
    unnestHead e@(AppE2 _ (Prim2 Pair _) 
                        (Var xt x) 
                        (Comp (ListT it) g (Quals [ BindQ y ys, GuardQ p])))
               qs@[BindQ x' xs] 
               | x == x' && 
                 -- The predicate must have the proper shape
                 isEquiJoinPred p &&
                 -- and must refer to x and y
                 freeVars p == S.fromList [x, y] &&
                 freeVars g == S.singleton y
                 = 
      case splitJoinPred p x y of
          Just (leftExpr, rightExpr) -> (headExpr, [BindQ x xs']) 
            where
              yt = elemT $ typeOf ys
              resType  = pairT xt (listT it)
              tupType  = pairT xt (listT yt)
              joinType = listT xt .-> (listT yt .-> listT tupType)
              
              -- snd x
              ys' = AppE1 (listT yt) (Prim1 Snd (tupType .-> (listT yt))) (Var tupType x)
              -- [ g | y <- snd x ]
              innerComp = Comp (listT it) g (Quals [BindQ y ys'])
  
              -- (fst x, innerComp)
              headExpr = AppE2 resType 
                               (Prim2 Pair (xt .-> (listT it .-> resType))) 
                               (AppE1 xt (Prim1 Fst (resType .-> xt)) (Var resType x))
                               innerComp
  
              xs'      = AppE2 (listT tupType) (Prim2 (NestJoin leftExpr rightExpr) joinType) xs ys
          Nothing -> (e, qs)
               
    unnestHead e qs = (e, qs)
  
unnestExistentials :: Expr -> Expr
unnestExistentials expr = transform go expr
  where
    go :: Expr -> Expr
    go (Comp t e (Quals qs)) = Comp t e (Quals qs') where qs' = unnestElem qs
    go e                     = e
    
    -- [ f x | x <- xs, or [ p | y <- ys ] ]
    unnestElem :: [Qual] -> [Qual]
    unnestElem qs@[ BindQ x xs
                  , GuardQ ((AppE1 _ (Prim1 Or _)
                                     (Comp _ p (Quals [BindQ y ys]))))
                  ] =
        case splitJoinPred p x y of
            Just (leftExpr, rightExpr) -> 
                let xst = typeOf xs
                    yst = typeOf ys
                    jt  = xst .-> yst .-> xst
                in [ BindQ x (AppE2 xst (Prim2 (SemiJoin leftExpr rightExpr) jt) xs ys) ]
                
            Nothing                    -> 
                qs
            
    unnestElem qs = qs
            
opt :: Expr -> Expr
opt e =
    if (e /= e') 
    then trace (printf "%s\n---->\n%s" (show e) (show e')) e'
    else trace (show e) e'
  where 
    e' = unnestExistentials $ unnestComprehensionHead $ introduceEquiJoins $ pushFilters e
-}

strategy :: RewriteC CL
strategy = anybuR (promoteR pushEquiFilters)

opt :: Expr -> Expr
opt expr = trace "foo" $ either (\msg -> trace msg expr) (\expr -> trace (show expr) expr) rewritten
  where
    rewritten = applyExpr (strategy >>> projectT) expr
