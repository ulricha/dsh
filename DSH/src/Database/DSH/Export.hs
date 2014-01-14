-- | Debug functions to export query plans and rendered database code
-- in various forms.
module Database.DSH.Export
  ( exportVLPlan
  , exportX100Plan
  , exportX100Code
  , exportSQL
  , exportTAPlan
  ) where

import           Database.Algebra.Dag
import           Database.Algebra.VL.Data                      hiding (Pair)
import           Database.Algebra.X100.Data
import           Database.Algebra.Pathfinder.Data.Algebra

import           Database.DSH.Common.Data.QueryPlan hiding (mkQueryPlan)
import           Database.DSH.Common.Data.DBCode

import qualified Database.Algebra.VL.Render.JSON               as VLJSON
import qualified Database.Algebra.X100.JSON                    as X100JSON
import qualified Database.Algebra.Pathfinder.Render.JSON       as PFJSON

exportVLPlan :: String -> QueryPlan VL -> IO ()
exportVLPlan prefix vlPlan = do
  let planPath = prefix ++ "_vl.plan"
      shapePath = prefix ++ "_vl.shape"

  VLJSON.planToFile planPath ( queryTags vlPlan
                             , rootsFromTopShape $ queryShape vlPlan
                             , nodeMap $ queryDag vlPlan
                             )
  writeFile shapePath $ show $ queryShape vlPlan

exportX100Plan :: String -> QueryPlan X100Algebra -> IO ()
exportX100Plan prefix x100Plan = do
  let planPath = prefix ++ "_x100.plan"
      shapePath = prefix ++ "_x100.shape"

  X100JSON.planToFile planPath ( queryTags x100Plan
                               , rootsFromTopShape $ queryShape x100Plan
                               , nodeMap $ queryDag x100Plan
                               )
  writeFile shapePath $ show $ queryShape x100Plan

exportTAPlan :: String -> QueryPlan PFAlgebra -> IO ()
exportTAPlan prefix pfPlan = do
  let planPath = prefix ++ "_ta.plan"
      shapePath = prefix ++ "_ta.shape"

  PFJSON.planToFile planPath ( queryTags pfPlan
                               , rootsFromTopShape $ queryShape pfPlan
                               , nodeMap $ queryDag pfPlan
                               )
  writeFile shapePath $ show $ queryShape pfPlan

query :: String -> String -> (a -> (Int, String)) -> TopShape a -> IO ()
query prefix suffix extract (ValueVector q l) = do
  let (i, s) = extract q
      f      = prefix ++ "_" ++ (show i) ++ suffix
  writeFile f s
  layout prefix suffix extract l
query prefix suffix extract (PrimVal q l)     = do
  let (i, s) = extract q
      f      = prefix ++ "_" ++ (show i) ++ suffix
  writeFile f s
  layout prefix suffix extract l

layout :: String -> String -> (a -> (Int, String)) -> TopLayout a -> IO ()
layout _      _      _        (InColumn _) = return ()
layout prefix suffix extract (Nest q l)   = do
  let (i, s) = extract q
      f      = prefix ++ "_" ++ (show i) ++ suffix
  writeFile f s
  layout prefix suffix extract l
layout prefix suffix extract (Pair l1 l2) = do
  layout prefix suffix extract l1
  layout prefix suffix extract l2

fromX100 :: X100Code -> (Int, String)
fromX100 (X100Code i s) = (i, s)

fromSQL :: SQLCode -> (Int, String)
fromSQL (SQLCode i _ s) = (i, s)

exportX100Code :: String -> TopShape X100Code -> IO ()
exportX100Code prefix q = query prefix ".vwq" fromX100 q

exportSQL :: String -> TopShape SQLCode -> IO ()
exportSQL prefix q = query prefix ".sql" fromSQL q
