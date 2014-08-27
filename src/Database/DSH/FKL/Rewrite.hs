module Database.DSH.FKL.Rewrite where

import Data.List

import Database.DSH.Common.Lang
import Database.DSH.Common.RewriteM
import Database.DSH.Common.Kure
import Database.DSH.FKL.Lang
import Database.DSH.FKL.Kure

-- | Run a translate on an expression without context
applyExpr :: TransformF Expr b -> Expr -> Either String b
applyExpr f e = runRewriteM $ apply f initialCtx (inject e)
