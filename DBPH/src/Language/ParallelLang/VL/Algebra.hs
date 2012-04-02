module Language.ParallelLang.VL.Algebra where

import qualified Language.ParallelLang.Common.Data.Type as U
import Database.Algebra.Dag.Common
import qualified Database.Algebra.Dag.Builder as G
import Database.Algebra.Pathfinder
import Language.ParallelLang.VL.Data.Query

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
