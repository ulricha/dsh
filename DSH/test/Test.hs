{-# LANGUAGE OverloadedStrings, QuasiQuotes, ViewPatterns #-}
module Test where

import Prelude()
import Database.DSH
import qualified Database.DSH.Flattening as I
import qualified Database.DSH.Compiler as C

import qualified Database.HDBC as HDBC
import Database.HDBC.PostgreSQL

import Data.Text (Text(..))

getConn :: IO Connection
getConn = connectPostgreSQL "user = 'postgres' password = 'haskell98' host = 'localhost' dbname = 'ferry'"

t :: IO ()
t = do
     conn <- getConn
     I.debugX100 conn $ groupWith (\(view -> (n, d, i)) -> d) employees
{-
test :: IO ()
test = do 
        conn <- getConn
        q <- I.debugPlan conn $ query
        putStrLn $ q    
-}
employees :: Q [(Text, Text, Integer)]
employees = toQ [
    ("Simon",  "MS",   80)
  , ("Erik",   "MS",   90)
  , ("Phil",   "Ed",   40)
  , ("Gordon", "Ed",   45)
  , ("Paul",   "Yale", 60)
  ]

{-
employees :: Q [(Text, Text)]
employees = toQ [("MS", "Bla")]
-}

{-
query :: Q [[Text]]
query = [$qc| dept
            | (dept, burp) <- employees
            , then group by dept
            |]
-}
{-
test :: IO ()
test = do
         conn <- getConn
         val <- I.fromQ conn $ Q.toQ [(1::Integer,2::Integer),(3,4),(5,6)]
         putStrLn $ show val
-}
{-
test :: IO ()
test = do
        conn <- getConn
        val <- I.debugPlan conn $ Q.map (Q.groupWith id) $ Q.toQ [[0,1,2,1::Integer], [0,3,1,0,3],[1,1]]
        putStrLn $ val

test2 :: IO ()
test2 = do
        conn <- getConn
        val <- I.fromQ conn $ Q.map (Q.map id) $ Q.toQ [[0,1,2,1::Integer], [0,3,1,0,3],[1,1]]
        putStrLn $ show val    
-}    
