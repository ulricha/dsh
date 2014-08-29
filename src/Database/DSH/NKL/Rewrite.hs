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
applyExpr nameCtx f e = runRewriteM $ apply f (initialCtx nameCtx) (inject e)

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
boundVarsT = fmap nub $ crushbuT $ do Comp _ _ v _ <- idR
                                      return [v]

-- | Compute all names that are bound in the given expression. Note
-- that the only binding form in NKL is a lambda.
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

substR :: Ident -> Expr -> RewriteN Expr
substR v s = readerT $ \expr -> case expr of
    -- Occurence of the variable to be replaced
    Var _ n | n == v                          -> return s

    -- Some other variable
    Var _ _                                   -> idR

    -- A comprehension which does not shadow v and in which v occurs
    -- free in the head. If the lambda variable occurs free in the
    -- substitute, we rename the lambda variable to avoid name
    -- capturing.
    Comp _ h x _ | x /= v && v `elem` freeVars h ->
        if x `elem` freeVars s
        then alphaCompR (freeVars s) >>> substR v s
        else anyR $ substR v s

    -- A comprehension whose generator shadows v -> don't descend into the head
    Comp _ _ x _ | v == x                     -> compR idR (substR v s)
    _                                         -> anyR $ substR v s

--------------------------------------------------------------------------------
-- Simple optimizations

pattern ConcatP t xs <- AppE1 t (Prim1 Concat _) xs
pattern SingletonP e <- AppE2 _ (Prim2 Cons _) e (Const _ (ListV []))
       
-- concatMap (\x -> [e x]) xs
-- concat [ [ e x ] | x <- xs ]
-- =>
-- [ e x | x <- xs ]
singletonHead :: RewriteN Expr
singletonHead = do
    ConcatP t (Comp _ (SingletonP e) x xs) <- idR
    return $ Comp t e x xs

nklOptimizations :: RewriteN Expr
nklOptimizations = anybuR singletonHead

optimizeNKL :: Expr -> Expr
optimizeNKL expr = debugOpt expr optimizedExpr
  where
    optimizedExpr = applyExpr [] nklOptimizations expr
        
