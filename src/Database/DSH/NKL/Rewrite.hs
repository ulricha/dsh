{-# LANGUAGE PatternSynonyms #-}

module Database.DSH.NKL.Rewrite
    ( substR
    , subst
    , freeVars
    , boundVars
    , optimizeNKL
    ) where

import Control.Arrow
import Data.List

import Database.DSH.Common.Type
import Database.DSH.Common.Lang
import Database.DSH.Common.Kure
import Database.DSH.Common.RewriteM
import Database.DSH.NKL.Kure
import Database.DSH.NKL.Lang

-- | Run a translate on an expression without context
applyExpr :: [Ident] -> TransformN Expr b -> Expr -> Either String b
applyExpr nameCtx f e = runRewriteM $ applyT f (initialCtx nameCtx) (inject e)

--------------------------------------------------------------------------------
-- Computation of free and bound variables

freeVarsT :: TransformN Expr [Ident]
freeVarsT = fmap nub $ crushbuT $ do (ctx, Var _ v) <- exposeT
                                     guardM (v `freeIn` ctx)
                                     return [v]

-- | Compute free variables of the given expression
freeVars :: Expr -> [Ident]
freeVars = either error id . applyExpr [] freeVarsT

boundVarsT :: TransformN Expr [Ident]
boundVarsT = fmap nub $ crushbuT $ readerT $ \expr -> case expr of
     Comp _ _ v _ -> return [v]
     Let _ v _ _  -> return [v]
     _            -> return []

-- | Compute all names that are bound in the given expression. Note
-- that the only binding forms in NKL are comprehensions or 'let'
-- bindings.
boundVars :: Expr -> [Ident]
boundVars = either error id . applyExpr [] boundVarsT

--------------------------------------------------------------------------------
-- Substitution

subst :: [Ident] -> Ident -> Expr -> Expr -> Expr
subst nameCtx x s e = either (const e) id $ applyExpr nameCtx (substR x s) e

alphaCompR :: [Ident] -> RewriteN Expr
alphaCompR avoidNames = do 
    Comp compTy h x _  <- idR
    x'                 <- freshNameT (x : freeVars h ++ avoidNames)
    let varTy = elemT compTy
    compT (tryR $ substR x (Var varTy x')) idR (\_ h' _ xs' -> Comp compTy h' x' xs')

alphaLetR :: [Ident] -> RewriteN Expr
alphaLetR avoidNames = do
    Let letTy x e1 e2 <- idR
    x'                <- freshNameT (x : freeVars e2 ++ avoidNames)
    let varTy = typeOf e1
    letT idR (tryR $ substR x (Var varTy x')) (\_ _ e1' e2' -> Let letTy x' e1' e2')

substR :: Ident -> Expr -> RewriteN Expr
substR v s = readerT $ \expr -> case expr of
    -- Occurence of the variable to be replaced
    Var _ n | n == v                          -> return s

    -- Some other variable
    Var _ _                                   -> idR

    -- A comprehension which does not shadow v and in which v occurs
    -- free in the head. If the comprehension variable occurs free in
    -- the substitute, we rename the comprehension to avoid name
    -- capturing.
    Comp _ h x _ | x /= v && v `elem` freeVars h ->
        if x `elem` freeVars s
        then alphaCompR (freeVars s) >>> substR v s
        else anyR $ substR v s

    -- A comprehension whose generator shadows v -> don't descend into the head
    Comp _ _ x _ | v == x                     -> compR idR (substR v s)

    Let _ x _ e2 | x /= v && v `elem` freeVars e2 ->
        if x `elem` freeVars s
        then alphaLetR (freeVars s) >>> substR v s
        else anyR $ substR v s

    -- A let binding which shadows v -> don't descend into the body
    Let _ x _ _ | v == x                      -> letR (substR v s) idR
    _                                         -> anyR $ substR v s

--------------------------------------------------------------------------------
-- Simple optimizations

pattern ConcatP t xs <- AppE1 t Concat xs
pattern SingletonP e <- AppE2 _ Cons e (Const _ (ListV []))
       
-- concatMap (\x -> [e x]) xs
-- concat [ [ e x ] | x <- xs ]
-- =>
-- [ e x | x <- xs ]
singletonHeadR :: RewriteN Expr
singletonHeadR = do
    ConcatP t (Comp _ (SingletonP e) x xs) <- idR
    return $ Comp t e x xs

-- | Count occurences of a given identifier.
countVarRefT :: Ident -> TransformN Expr Int
countVarRefT n = do
    refs <- collectT $ do Var _ n' <- idR
                          guardM $ n == n'
                          return n'
    return $ length refs

-- | Remove a let-binding that is not referenced.
unusedBindingR :: RewriteN Expr
unusedBindingR = do
    Let _ x _ e2 <- idR
    0            <- childT LetBody $ countVarRefT x
    return $ e2

-- | Inline a let-binding that is only referenced once.
referencedOnceR :: RewriteN Expr
referencedOnceR = do
    Let _ x e1 _ <- idR
    1             <- childT LetBody $ countVarRefT x
    childT LetBody $ substR x e1

simpleExpr :: Expr -> Bool
simpleExpr Table{} = True
simpleExpr Var{}   = True
simpleExpr _       = False

-- | Inline a let-binding that binds a simple expression.
simpleBindingR :: RewriteN Expr
simpleBindingR = do
    Let _ x e1 _ <- idR
    guardM $ simpleExpr e1
    childT LetBody $ substR x e1
    
nklOptimizations :: RewriteN Expr
nklOptimizations = anybuR $ singletonHeadR 
                            <+ unusedBindingR 
                            <+ referencedOnceR
                            <+ simpleBindingR

optimizeNKL :: Expr -> Expr
optimizeNKL expr = debugOpt "NKL" expr optimizedExpr
  where
    optimizedExpr = applyExpr [] nklOptimizations expr
        
