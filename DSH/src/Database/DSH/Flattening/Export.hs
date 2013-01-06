module Database.DSH.Flattening.Export
  ( exportVLPlan
  , exportX100Plan
  , exportX100Code
  , exportPFXML
  , exportSQL
  ) where

import           Database.Algebra.Dag
import           Database.Algebra.VL.Data                      hiding (Pair)
import           Database.Algebra.X100.Data

import           Database.DSH.Flattening.Common.Data.QueryPlan hiding (mkQueryPlan)
import qualified Database.DSH.Flattening.VL.Data.Query         as Q

import qualified Database.Algebra.VL.Render.JSON               as VLJSON
import qualified Database.Algebra.X100.JSON                    as X100JSON

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

query :: String -> String -> (a -> (Int, String)) -> Q.Query a -> IO ()
query prefix suffix extract (Q.ValueVector q l) = do
  let (i, s) = extract q
      f      = prefix ++ "_" ++ (show i) ++ suffix
  writeFile f s
  layout prefix suffix extract l
query prefix suffix extract (Q.PrimVal q l)     = do
  let (i, s) = extract q
      f      = prefix ++ "_" ++ (show i) ++ suffix
  writeFile f s
  layout prefix suffix extract l

layout :: String -> String -> (a -> (Int, String)) -> Q.Layout a -> IO ()
layout _      _      _        (Q.InColumn _) = return ()
layout prefix suffix extract (Q.Nest q l)   = do
  let (i, s) = extract q
      f      = prefix ++ "_" ++ (show i) ++ suffix
  writeFile f s
  layout prefix suffix extract l
layout prefix suffix extract (Q.Pair l1 l2) = do
  layout prefix suffix extract l1
  layout prefix suffix extract l2

fromXML :: Q.XML -> (Int, String)
fromXML (Q.XML i s) = (i, s)

fromX100 :: Q.X100 -> (Int, String)
fromX100 (Q.X100 i s) = (i, s)

fromSQL :: Q.SQL -> (Int, String)
fromSQL (Q.SQL i _ s) = (i, s)

exportX100Code :: String -> Q.Query Q.X100 -> IO ()
exportX100Code prefix q = query prefix ".vwq" fromX100 q

exportPFXML :: String -> Q.Query Q.XML -> IO ()
exportPFXML prefix q = query prefix ".xml" fromXML q

exportSQL :: String -> Q.Query Q.SQL -> IO ()
exportSQL prefix q = query prefix ".sql" fromSQL q
