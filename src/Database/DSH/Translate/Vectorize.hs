module Database.DSH.Translate.Vectorize where

import Database.DSH.Common.QueryPlan
import Database.DSH.Common.Vector
import Database.DSH.Common.VectorLang
import Database.DSH.FKL.Lang

class VectorLang v where
    vectorize :: FExpr -> QueryPlan (v TExpr TExpr) DVec
    optimizeVectorPlan :: QueryPlan (v TExpr TExpr) DVec -> QueryPlan (v TExpr TExpr) DVec
