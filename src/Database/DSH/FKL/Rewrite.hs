module Database.DSH.FKL.Rewrite where

import Database.DSH.Common.RewriteM
import Database.DSH.FKL.Lang
import Database.DSH.FKL.Kure

-- | Run a translate on an expression without context
applyExpr :: TransformF (Expr l) b -> Expr l -> Either String b
applyExpr f e = runRewriteM $ applyT f initialCtx (inject e)
