-- | Debug functions to export query plans and rendered database code
-- in various forms.
module Database.DSH.Export
  ( exportVLPlan
  , exportTAPlan
  ) where

import           Database.Algebra.Dag
import           Database.Algebra.Table.Lang
import qualified Database.Algebra.Table.Render.JSON as PFJSON

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

exportTAPlan :: String -> QueryPlan TableAlgebra NDVec -> IO ()
exportTAPlan prefix pfPlan = do
  let planPath = prefix ++ "_ta.plan"
      shapePath = prefix ++ "_ta.shape"

  PFJSON.planToFile planPath ( queryTags pfPlan
                             , shapeNodes $ queryShape pfPlan
                             , nodeMap $ queryDag pfPlan
                             )
  writeFile shapePath $ show $ queryShape pfPlan
