module Database.DSH.Translate.Vectorize where

import Database.DSH.Common.QueryPlan
import Database.DSH.Common.Vector
import Database.DSH.FKL.Lang

class VectorLang v where
    vectorize :: FExpr -> QueryPlan v DVec
    optimizeVectorPlan :: QueryPlan v DVec -> QueryPlan v DVec
