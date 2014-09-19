{-# LANGUAGE FlexibleContexts #-}

module Database.DSH.FKL.Rewrite
    ( optimizeFKL
    ) where

import Data.List
import Control.Arrow

import Database.DSH.Common.RewriteM
import Database.DSH.Common.Lang
import Database.DSH.Common.Type
import Database.DSH.Common.Kure
import Database.DSH.Common.Pretty
import Database.DSH.FKL.Lang
import Database.DSH.FKL.Kure

-- | Run a translate on an expression without context
applyExpr :: TransformF (Expr l) b -> Expr l -> Either String b
applyExpr f e = runRewriteM $ applyT f initialCtx e

--------------------------------------------------------------------------------
-- Computation of free and bound variables

freeVarsT :: TransformF (Expr l) [Ident]
freeVarsT = fmap nub $ crushbuT $ do (ctx, Var _ v) <- exposeT
                                     guardM (v `freeIn` ctx)
                                     return [v]

-- | Compute free variables of the given expression
freeVars :: Expr l -> [Ident]
freeVars = either error id . applyExpr freeVarsT

--------------------------------------------------------------------------------
-- Substitution

alphaLetR :: [Ident] -> RewriteF (Expr l)
alphaLetR avoidNames = do
    Let letTy x e1 e2 <- idR
    x'                <- freshNameT (x : freeVars e2 ++ avoidNames)
    let varTy = typeOf e1
    letT idR (tryR $ substR x (Var varTy x')) (\_ _ e1' e2' -> Let letTy x' e1' e2')

substR :: Ident -> Expr l -> RewriteF (Expr l)
substR v s = readerT $ \expr -> case expr of
    -- Occurence of the variable to be replaced
    Var _ n | n == v                          -> return s

    -- Some other variable
    Var _ _                                   -> idR

    Let _ x _ e2 | x /= v && v `elem` freeVars e2 ->
        if x `elem` freeVars s
        then alphaLetR (freeVars s) >>> substR v s
        else anyR $ substR v s

    -- A let binding which shadows v -> don't descend into the body
    Let _ x _ _ | v == x                      -> letR (substR v s) idR
    _                                         -> anyR $ substR v s



--------------------------------------------------------------------------------
-- Simple optimizations

-- | Count occurences of a given identifier.
countVarRefT :: Ident -> TransformF (Expr l) Int
countVarRefT n = do
    refs <- collectT $ do Var _ n' <- idR
                          guardM $ n == n'
                          return n'
    return $ length refs

-- | Remove a let-binding that is not referenced.
unusedBindingR :: RewriteF (Expr l)
unusedBindingR = do
    Let _ x _ e2 <- idR
    0            <- childT LetBody $ countVarRefT x
    return $ e2

-- | Inline a let-binding that is only referenced once.
referencedOnceR :: RewriteF (Expr l)
referencedOnceR = do
    Let _ x e1 _ <- idR
    1            <- childT LetBody $ countVarRefT x
    childT LetBody $ substR x e1

simpleExpr :: (Expr l) -> Bool
simpleExpr Table{} = True
simpleExpr Var{}   = True
simpleExpr _       = False

-- | Inline a let-binding that binds a simple expression.
simpleBindingR :: RewriteF (Expr l)
simpleBindingR = do
    Let _ x e1 _ <- idR
    guardM $ simpleExpr e1
    childT LetBody $ substR x e1
    
fklOptimizations :: RewriteF (Expr l)
fklOptimizations = anybuR $ unusedBindingR 
                            <+ referencedOnceR
                            <+ simpleBindingR

optimizeFKL :: Pretty (Expr l) => Expr l -> (Expr l)
optimizeFKL expr = debugOpt expr optimizedExpr
  where
    optimizedExpr = applyExpr fklOptimizations expr
        
