module Language.ParallelLang.VL.Algebra where

import qualified Language.ParallelLang.Common.Data.Type as U
--import Database.Ferry.Algebra hiding (getLoop, withContext, Gam)
import Database.Algebra.Graph.Common
import qualified Database.Algebra.Graph.GraphBuilder as G
import Database.Algebra.Pathfinder
--import qualified Database.Ferry.Algebra as A
import Language.ParallelLang.VL.Data.Query

--type Graph = GraphM Plan
type Graph a = G.GraphM Plan a

type Gam = G.Gam Plan

type Plan = Query AlgNode

convertType :: U.Type -> ATy
convertType t | t == U.intT  = intT
              | t == U.boolT = boolT
              | t == U.unitT = intT
              | t == U.stringT = stringT
              | t == U.doubleT = doubleT
              | otherwise = error "convertType: Can't convert from DBPH type to Ferry types"
