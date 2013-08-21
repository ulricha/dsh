module Database.DSH.CL.OptUtils where

import Control.Applicative
import Control.Arrow
import Control.Monad

import Data.List

import Database.DSH.CL.Lang
import Database.DSH.CL.Monad
import Database.DSH.CL.Kure
       

{-
applyCL :: (String -> b) -> TranslateC CL b -> CL -> b
applyCL err f = runKureM id err . apply f initialCtx
-}

applyExpr :: TranslateC CL b -> Expr -> Either String b
applyExpr f e = runCompM $ apply f initialCtx (inject e)

--------------------------------------------------------------------------------
-- Computation of free variables

freeVarsT :: TranslateC CL [Ident]
freeVarsT = fmap nub $ crushbuT $ promoteT $ do (ctx, Var _ v) <- exposeT
                                                guardM (v `freeIn` ctx)
                                                return [v]
                                                
freeVars :: Expr -> [Ident]
freeVars = either error id . applyExpr freeVarsT

--------------------------------------------------------------------------------
-- Substitution

alphaLam :: RewriteC Expr
alphaLam = do (ctx, Lam lamTy v e) <- exposeT
              v' <- constT $ freshName (inScopeVars ctx)
              let varTy = domainT lamTy
              lamT (extractR $ tryR $ subst v (Var varTy v')) (\_ _ -> Lam lamTy v')
              
nonBinder :: Expr -> Bool
nonBinder expr =
    case expr of
        Lam _ _ _  -> False
        Var _ _    -> False
        Comp _ _ _ -> False
        _          -> True
                                                
subst :: Ident -> Expr -> RewriteC CL
subst v s = rules_var <+ rules_lam <+ rules_nonbind
  where
    rules_var :: RewriteC CL
    rules_var = do Var _ n <- promoteT idR
                   guardM (n == v)
                   return $ inject s
    
    rules_lam :: RewriteC CL
    rules_lam = do (ctx, Lam _ n e) <- promoteT exposeT
                   guardM (n /= v)
                   guardM $ v `elem` freeVars e
                   if n `elem` freeVars s
                       then promoteR alphaLam >>> rules_lam
                       else promoteR $ lamR (extractR $ subst v s)
                       
    rules_comp :: RewriteC CL
    rules_comp = do Comp ty e qs <- promoteT idR
                    undefined
                       
    rules_nonbind :: RewriteC CL
    rules_nonbind = do guardMsgM (nonBinder <$> promoteT idR) "binding node"
                       anyR (subst v s)
