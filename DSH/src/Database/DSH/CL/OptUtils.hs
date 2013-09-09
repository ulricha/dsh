{-# LANGUAGE FlexibleContexts #-}
-- | Some utilities for KURE-based transformations on CL expressions

module Database.DSH.CL.OptUtils
    ( applyExpr
    , freeVars
    , compBoundVars
    , substR
    , tuplifyR
    , onetdSpineT
    ) where

import           Control.Applicative
import           Control.Arrow
       
import           Debug.Trace

import           Data.List
import qualified Data.Foldable as F

import           Database.DSH.CL.Lang
import           Database.DSH.CL.Monad
import           Database.DSH.CL.Kure
       

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

compBoundVars :: F.Foldable f => f Qual -> [Ident]
compBoundVars qs = F.foldr aux [] qs
  where 
    aux :: Qual -> [Ident] -> [Ident]
    aux (BindQ n _) ns = n : ns
    aux (GuardQ _) ns  = ns

--------------------------------------------------------------------------------
-- Substitution

alphaLamR :: RewriteC Expr
alphaLamR = do (ctx, Lam lamTy v _) <- exposeT
               v' <- constT $ freshName (inScopeVars ctx)
               let varTy = domainT lamTy
               lamT (extractR $ tryR $ substR v (Var varTy v')) (\_ _ -> Lam lamTy v')
              
nonBinder :: Expr -> Bool
nonBinder expr =
    case expr of
        Lam _ _ _  -> False
        Var _ _    -> False
        Comp _ _ _ -> False
        _          -> True
                                                
substR :: Ident -> Expr -> RewriteC CL
substR v s = rules_var <+ rules_lam <+ rules_nonbind <+ rules_comp <+ rules_quals <+ rules_qual
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
                       then promoteR alphaLamR >>> rules_lam
                       else promoteR $ lamR (extractR $ substR v s)
                       
    rules_comp :: RewriteC CL
    rules_comp = do Comp _ _ qs <- promoteT idR
                    if v `elem` compBoundVars qs
                        then promoteR $ compR idR (extractR $ substR v s)
                        else promoteR $ compR (extractR $ substR v s) (extractR $ substR v s)
                       
    rules_nonbind :: RewriteC CL
    rules_nonbind = do guardMsgM (nonBinder <$> promoteT idR) "binding node"
                       anyR (substR v s)
                       
    rules_quals :: RewriteC CL
    rules_quals = do qs <- promoteT idR
                     case qs of
                         (BindQ n _) :* _ -> do
                             if n == v
                                 -- the current binding shadows the variable to be replaced
                                 -- => don't descent into the tail
                                 then promoteR $ qualsR (extractR $ substR v s) idR
                                 -- no shadowing, descend into the tail
                                 else promoteR $ qualsR (extractR $ substR v s) (extractR $ substR v s)
                         _ :* _           -> do
                             promoteR $ qualsR (extractR $ substR v s) (extractR $ substR v s)
                         S _              -> do
                             promoteR $ qualsemptyR (extractR $ substR v s)
    
    rules_qual :: RewriteC CL
    rules_qual = anyR (substR v s)

--------------------------------------------------------------------------------
-- Tuplifying variables

tuplifyR :: Ident -> (Ident, Type) -> (Ident, Type) -> RewriteC CL
tuplifyR v (v1, t1) (v2, t2) = substR v1 v1Rep >+> substR v2 v2Rep
  where 
    (v1Rep, v2Rep) = tupleVars v t1 t2

tupleVars :: Ident -> Type -> Type -> (Expr, Expr)
tupleVars n t1 t2 = (v1Rep, v2Rep)
  where v     = Var pt n
        pt    = pairT t1 t2
        v1Rep = AppE1 t1 (Prim1 Fst (pt .-> t1)) v
        v2Rep = AppE1 t2 (Prim1 Snd (pt .-> t2)) v

--------------------------------------------------------------------------------
-- Traversal functions

-- | Traverse the spine of a NL list top-down and apply the translation as soon
-- as possible.
onetdSpineT 
  :: (ReadPath c Int, MonadCatch m, Walker c CL) 
  => Translate c m CL b 
  -> Translate c m CL b
onetdSpineT t = do
    n <- idR
    case n of
        QualsCL (_ :* _) -> childT 0 t <+ childT 1 (onetdSpineT t)
        QualsCL (S _)    -> childT 0 t
        
