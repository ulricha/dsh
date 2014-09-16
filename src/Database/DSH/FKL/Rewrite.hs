module Database.DSH.FKL.Rewrite where

import Data.List

import Database.DSH.Common.Lang
import Database.DSH.Common.RewriteM
import Database.DSH.Common.Kure
import Database.DSH.FKL.Lang
import Database.DSH.FKL.Pretty()
import Database.DSH.FKL.Kure

-- | Run a translate on an expression without context
applyExpr :: TransformF Expr b -> Expr -> Either String b
applyExpr f e = runRewriteM $ apply f initialCtx (inject e)

--------------------------------------------------------------------------------
-- Computation of free and bound variables

freeVarsT :: TransformF Expr [Ident]
freeVarsT = fmap nub $ crushbuT $ promoteT $ do (ctx, Var _ v) <- exposeT
                                                guardM (v `freeIn` ctx)
                                                return [v]

-- | Compute free variables of the given expression
freeVars :: Expr -> [Ident]
freeVars = either error id . applyExpr freeVarsT

--------------------------------------------------------------------------------
-- Substitution

subst :: Ident -> Expr -> Expr -> Expr
subst x s e = either (const e) id $ applyExpr (substR x s) e

substR :: Ident -> Expr -> RewriteF Expr
substR v s = readerT $ \expr -> case expr of
    -- Occurence of the variable to be replaced
    Var _ n | n == v                          -> return $ inject s

    -- Some other variable
    Var _ _                                   -> idR

    -- A closure is closed by definition. There are no opportunities
    -- for substitution in its body.  FIXME this is not correct. Have
    -- to descend into the body when the variable that is substituted
    -- occurs in the closure environment.
    Clo _ _ _ _ _ _                           -> fail "subst clo"
    AClo _ _ _ _ _ _                          -> fail "subst aclo"

    _                                         -> anyR $ substR v s

--------------------------------------------------------------------------------
-- Simple optimizations

applyEmptyClosureR :: RewriteF Expr
applyEmptyClosureR = do
    CloApp _ (Clo _ _ [] x body _) arg <- idR
    debugMsg "Trigger applyEmptyClosureR"
    return $ subst x arg body

fklOptimizations :: RewriteF Expr
fklOptimizations = anybuR applyEmptyClosureR

optimizeFKL :: Expr -> Expr
optimizeFKL expr = debugOpt expr optimizedExpr
  where
    optimizedExpr = applyExpr fklOptimizations expr
    
