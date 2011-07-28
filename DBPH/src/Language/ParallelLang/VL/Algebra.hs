module Language.ParallelLang.VL.Algebra where

import qualified Language.ParallelLang.Common.Data.Type as U
import Database.Ferry.Algebra hiding (getLoop, withContext, Gam)
import qualified Database.Ferry.Algebra as A
import Language.ParallelLang.VL.Data.Query

type Graph = GraphM Plan

type Gam = A.Gam Plan

type Plan = Query AlgNode

-- | Results are stored in column:
pos, item1, descr, descr', descr'', pos', pos'', pos''', posold, posnew, ordCol, resCol, tmpCol, tmpCol' :: String
pos       = "pos"
item1     = "item1"
descr     = "iter"
descr'    = "item99999501"
descr''   = "item99999502"
pos'      = "item99999601"
pos''     = "item99999602"
pos'''    = "item99999603"
posold    = "item99999604"
posnew    = "item99999605"
ordCol    = "item99999801"
resCol    = "item99999001"
tmpCol    = "item99999002"
tmpCol'   = "item99999003"

convertType :: U.Type -> ATy
convertType t | t == U.intT  = intT
              | t == U.boolT = boolT
              | t == U.unitT = intT
              | t == U.stringT = stringT
              | t == U.doubleT = doubleT
              | otherwise = error "convertType: Can't convert from DBPH type to Ferry types"