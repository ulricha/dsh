-- | Some utilities for KURE-based transformations on CL expressions

module Database.DSH.CL.OptUtils
    ( applyExpr
    , freeVarsT, freeVars
    , subst
    , tuplify
    ) where

import Control.Applicative
import Control.Arrow

import Data.List
import qualified Data.Foldable as F

import Database.DSH.CL.Lang
import Database.DSH.CL.Monad
import Database.DSH.CL.Kure
       

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

compBoundVars :: NL Qual -> [Ident]
compBoundVars qs = F.foldr aux [] qs
  where 
    aux :: Qual -> [Ident] -> [Ident]
    aux (BindQ n _) ns = n : ns
    aux (GuardQ _) ns  = ns

--------------------------------------------------------------------------------
-- Substitution

alphaLam :: RewriteC Expr
alphaLam = do (ctx, Lam lamTy v _) <- exposeT
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
subst v s = rules_var <+ rules_lam <+ rules_nonbind <+ rules_comp <+ rules_quals <+ rules_qual
  where
    rules_var :: RewriteC CL
    rules_var = do Var _ n <- promoteT idR
                   guardM (n == v)
                   return $ inject s
    
    rules_lam :: RewriteC CL
    rules_lam = do Lam _ n e <- promoteT idR
                   guardM (n /= v)
                   guardM $ v `elem` freeVars e
                   if n `elem` freeVars s
                       then promoteR alphaLam >>> rules_lam
                       else promoteR $ lamR (extractR $ subst v s)
                       
    rules_comp :: RewriteC CL
    rules_comp = do Comp _ _ qs <- promoteT idR
                    if v `elem` compBoundVars qs
                        then promoteR $ compR idR (extractR $ subst v s)
                        else promoteR $ compR (extractR $ subst v s) (extractR $ subst v s)
                       
    rules_nonbind :: RewriteC CL
    rules_nonbind = do guardMsgM (nonBinder <$> promoteT idR) "binding node"
                       anyR (subst v s)
                       
    rules_quals :: RewriteC CL
    rules_quals = do qs <- promoteT idR
                     case qs of
                         (BindQ n _) :* _ -> do
                             guardM $ n == v
                             promoteR $ qualsR (extractR $ subst v s) idR
                         _ :* _           -> do
                             promoteR $ qualsR (extractR $ subst v s) (extractR $ subst v s)
                         S _              -> do
                             promoteR $ qualsemptyR (extractR $ subst v s)
    
    rules_qual :: RewriteC CL
    rules_qual = do QualCL _ <- idR
                    anyR (subst v s)


--------------------------------------------------------------------------------
-- Tuplifying variables

tuplify :: Ident -> (Ident, Type) -> (Ident, Type) -> RewriteC CL
tuplify v (v1, t1) (v2, t2) = subst v1 v1Rep >>> subst v2 v2Rep
  where 
    (v1Rep, v2Rep) = tupleVars v t1 t2

tupleVars :: Ident -> Type -> Type -> (Expr, Expr)
tupleVars n t1 t2 = (v1Rep, v2Rep)
  where v     = Var pt n
        pt    = pairT t1 t2
        v1Rep = AppE1 t1 (Prim1 Fst (pt .-> t1)) v
        v2Rep = AppE1 t2 (Prim1 Snd (pt .-> t2)) v
