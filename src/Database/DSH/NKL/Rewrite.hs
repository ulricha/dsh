module Database.DSH.NKL.Rewrite
    ( substR
    , freeVars
    ) where

import Control.Arrow
import Data.List

import Database.DSH.Common.Type
import Database.DSH.Common.Lang
import Database.DSH.Common.RewriteM
import Database.DSH.NKL.Kure
import Database.DSH.NKL.Lang

-- | Run a translate on an expression without context
applyExpr :: TransformN Expr b -> Expr -> Either String b
applyExpr f e = runRewriteM $ apply f initialCtx (inject e)

--------------------------------------------------------------------------------
-- Computation of free variables

freeVarsT :: TransformN Expr [Ident]
freeVarsT = fmap nub $ crushbuT $ promoteT $ do (ctx, Var _ v) <- exposeT
                                                guardM (v `freeIn` ctx)
                                                return [v]

-- | Compute free variables of the given expression
freeVars :: Expr -> [Ident]
freeVars = either error id . applyExpr freeVarsT

--------------------------------------------------------------------------------
-- Substitution

alphaLamR :: RewriteN Expr
alphaLamR = do 
    Lam lamTy v _ <- idR
    v'            <- freshNameT [v]
    let varTy = domainT lamTy
    lamT (extractR $ tryR $ substR v (Var varTy v')) (\_ _ -> Lam lamTy v')

substR :: Ident -> Expr -> RewriteN Expr
substR v s = readerT $ \e -> case e of
    -- Occurence of the variable to be replaced
    Var _ n | n == v                          -> return $ inject s

    -- Some other variable
    Var _ _                                   -> idR

    -- A lambda which does not shadow v and in which v occurs free. If the
    -- lambda variable occurs free in the substitute, we rename the lambda
    -- variable to avoid name capturing.
    Lam _ n e | n /= v && v `elem` freeVars e ->
        if n `elem` freeVars s
        then promoteR alphaLamR >>> substR v s
        else promoteR $ lamR (extractR $ substR v s)

    -- A lambda which shadows v -> don't descend
    Lam _ _ _                                 -> idR
