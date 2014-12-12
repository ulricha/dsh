-- | Debug functions to export query plans and rendered database code
-- in various forms.
module Database.DSH.Export
  ( exportVLPlan
  , exportX100Plan
  , exportTAPlan
  ) where

import           Database.Algebra.Dag
import           Database.Algebra.Table.Lang
import qualified Database.Algebra.Table.Render.JSON as PFJSON
import           Database.Algebra.X100.Data
import qualified Database.Algebra.X100.JSON         as X100JSON

import           Database.DSH.Common.QueryPlan
import           Database.DSH.VL.Lang
import           Database.DSH.VL.Vector
import qualified Database.DSH.VL.Render.JSON        as VLJSON

exportVLPlan :: String -> QueryPlan VL VLDVec -> IO ()
exportVLPlan prefix vlPlan = do
  let planPath = prefix ++ "_vl.plan"
      shapePath = prefix ++ "_vl.shape"

  VLJSON.planToFile planPath ( queryTags vlPlan
                             , shapeNodes $ queryShape vlPlan
                             , nodeMap $ queryDag vlPlan
                             )
  writeFile shapePath $ show $ queryShape vlPlan

exportX100Plan :: String -> QueryPlan X100Algebra NDVec -> IO ()
exportX100Plan prefix x100Plan = do
  let planPath = prefix ++ "_x100.plan"
      shapePath = prefix ++ "_x100.shape"

  X100JSON.planToFile planPath ( queryTags x100Plan
                               , shapeNodes $ queryShape x100Plan
                               , nodeMap $ queryDag x100Plan
                               )
  writeFile shapePath $ show $ queryShape x100Plan

exportTAPlan :: String -> QueryPlan TableAlgebra NDVec -> IO ()
exportTAPlan prefix pfPlan = do
  let planPath = prefix ++ "_ta.plan"
      shapePath = prefix ++ "_ta.shape"

  PFJSON.planToFile planPath ( queryTags pfPlan
                             , shapeNodes $ queryShape pfPlan
                             , nodeMap $ queryDag pfPlan
                             )
  writeFile shapePath $ show $ queryShape pfPlan
