{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.NKL.Rewrite
    ( substR
    , subst
    , freeVars
    , boundVars
    , optimizeNKL
    ) where

import Control.Arrow
import Data.List
import Data.Monoid

import Database.DSH.Impossible
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
     Iterator _ _ v _ -> return [v]
     Let _ v _ _      -> return [v]
     _                -> return []

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
    Iterator compTy h x _  <- idR
    x'                     <- freshNameT (x : freeVars h ++ avoidNames)
    let varTy = elemT compTy
    iteratorT (tryR $ substR x (Var varTy x')) 
              idR 
              (\_ h' _ xs' -> Iterator compTy h' x' xs')

alphaLetR :: [Ident] -> RewriteN Expr
alphaLetR avoidNames = do
    Let letTy x e1 e2 <- idR
    x'                <- freshNameT (x : freeVars e2 ++ avoidNames)
    let varTy = typeOf e1
    letT idR (tryR $ substR x (Var varTy x')) (\_ _ e1' e2' -> Let letTy x' e1' e2')

-- | Replace /all/ references to variable 'v' by expression 's'.
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
    Iterator _ h x _ | x /= v && v `elem` freeVars h ->
        if x `elem` freeVars s
        then alphaCompR (freeVars s) >>> substR v s
        else anyR $ substR v s

    -- A comprehension whose generator shadows v -> don't descend into the head
    Iterator _ _ x _ | v == x                     -> iteratorR idR (substR v s)

    Let _ x _ e2 | x /= v && v `elem` freeVars e2 ->
        if x `elem` freeVars s
        then alphaLetR (freeVars s) >>> substR v s
        else anyR $ substR v s

    -- A let binding which shadows v -> don't descend into the body
    Let _ x _ _ | v == x                      -> letR (substR v s) idR
    _                                         -> anyR $ substR v s

--------------------------------------------------------------------------------
-- Simple optimizations

-- | This function inlines let-bound expressions. In contrast to
-- general substitution, we do not inline into comprehensions, even if
-- we could. The reason is that expressions should not be evaluated
-- iteratively if they are loop-invariant.
inlineBindingR :: Ident -> Expr -> RewriteN Expr
inlineBindingR v s = readerT $ \expr -> case expr of
    -- Occurence of the variable to be replaced
    Var _ n | n == v          -> return $ inject s

    -- If a let-binding shadows the name we substitute, only descend
    -- into the bound expression.
    Let _ n _ _ | n == v      -> promoteR $ letR idR (extractR $ inlineBindingR v s)
    Let _ n _ _ | otherwise   ->
        if n `elem` freeVars s
        -- If the let-bound name occurs free in the substitute,
        -- alpha-convert the binding to avoid capturing the name.
        then $unimplemented >>> anyR (inlineBindingR v s)
        else anyR $ inlineBindingR v s

    -- We don't inline into comprehensions to avoid conflicts with
    -- loop-invariant extraction.
    Iterator _ _ _ _          -> idR
    _                         -> anyR $ inlineBindingR v s

pattern ConcatP t xs <- AppE1 t Concat xs
pattern SingletonP e <- AppE1 _ Singleton e 
       
-- concatMap (\x -> [e x]) xs
-- concat [ [ e x ] | x <- xs ]
-- =>
-- [ e x | x <- xs ]
singletonHeadR :: RewriteN Expr
singletonHeadR = do
    ConcatP t (Iterator _ (SingletonP e) x xs) <- idR
    return $ Iterator t e x xs

-- | Count all occurences of an identifier for let-inlining.
countVarRefT :: Ident -> TransformN Expr (Sum Int)
countVarRefT v = readerT $ \expr -> case expr of
    -- Occurence of the variable to be replaced
    Var _ n | n == v         -> return 1
    Var _ _ | otherwise      -> return 0

    Let _ n _ _ | n == v     -> letT (constT $ return 0) 
                                     (countVarRefT v)
                                     (\_ _ c1 c2 -> c1 + c2)
    Let _ _ _ _ | otherwise  -> letT (countVarRefT v)
                                     (countVarRefT v)
                                     (\_ _ c1 c2 -> c1 + c2)

    Iterator _ _ x _ | v == x -> iteratorT (constT $ return 0)
                                           (countVarRefT v)
                                           (\_ c1 _ c2 -> c1 + c2)
    Iterator _ _ _ _ | otherwise -> iteratorT (countVarRefT v)
                                              (countVarRefT v)
                                              (\_ c1 _ c2 -> c1 + c2)

    Table{}                  -> return 0
    Const{}                  -> return 0
    _                        -> allT (countVarRefT v)

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
    1            <- childT LetBody $ countVarRefT x

    -- We do not inline into comprehensions, but 'countVarRef' counts
    -- all occurences including those in comprehensions. For this
    -- reason, we check if the occurence was actually eliminated by
    -- inlining and fail otherwise.
    body' <- childT LetBody (inlineBindingR x e1)
    0     <- (constT $ return body') >>> countVarRefT x
    return body'

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
        
