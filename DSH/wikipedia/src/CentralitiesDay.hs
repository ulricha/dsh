module Main where

import Database.DSH (csvExport)
import qualified Data.IGraph as Graph
import Database.PostgreSQL.Simple
import System.Environment (getArgs)
import System.Directory (doesFileExist)
import Data.String
-- import qualified Data.Map as Map

getEdges :: Double -> IO [(Integer,Integer)]
getEdges day = do
  conn   <- connect (defaultConnectInfo{connectUser = "giorgidz", connectDatabase = "giorgidz"})
  result <- query_ conn (fromString ("SELECT link_from_page, link_to_page FROM links WHERE link_added < " ++ show day ++ " AND link_removed > " ++  show day ++ " "))
  close conn
  return result

getPageIds :: IO [Integer]
getPageIds = do
  conn   <- connect (defaultConnectInfo{connectUser = "giorgidz", connectDatabase = "giorgidz"})
  result <- query_ conn (fromString ("SELECT DISTINCT scp_page FROM super_category_pages"))
  close conn
  return (map fromOnly result)

main :: IO ()
main = do
  args <- getArgs
  let day = case args of
              []      -> error "usage: dsh-wikipedia-centralities-day epoch_time_stamp"
              (s : _) -> read s

  let file = "shortest_path_stats_" ++ show day ++ ".csv"
  
  rEdges   <- getEdges day
  rPageIds <- getPageIds
  let rGraph = Graph.make rEdges
  let na     = -99 :: Integer
  let nad    = -99 :: Double
  let result =  [ if Graph.member rGraph pid
                     then ( day
                          , pid
                          , fromIntegral (length paths)
                          , fromIntegral (sum (map length paths)) / fromIntegral (length paths)
                          , fromIntegral (maximum (map length paths))
                          )
                     else (day, pid, na, nad, na)
                | pid <- rPageIds
                , let paths = Graph.shortestPathsIn rGraph pid
                ]

  csvExport file result
  -- b <- doesFileExist file
  -- if b
  --    then return ()
  --    else csvExport file result
