{-# LANGUAGE OverloadedStrings, QuasiQuotes, ViewPatterns #-}
module Test where

import Prelude()
import qualified Prelude as P
import Database.DSH
import qualified Database.DSH.Flattening as I
import qualified Database.DSH.Compiler as C

import qualified Database.HDBC as HDBC
import Database.HDBC.PostgreSQL

import Data.Text (Text(..), pack)

import Database.X100Client

getConn :: IO Connection
getConn = connectPostgreSQL "user = 'postgres' password = 'haskell98' host = 'localhost' dbname = 'ferry'"

getXConn :: IO X100Info
getXConn = P.return $ x100Info "localhost" 48130 Nothing

expr :: Q [[[Integer]]]
expr = map (sortWith length) $ toQ [] -- toQ [[[0], [0::Integer]],[[1]],[[2],[2],[3]]]

t' :: IO ()
t' = do
      conn <- getXConn
      I.debugX100 conn expr
      r <- I.debugNKLX100 conn expr
      putStrLn r
      r <- I.fromX100 conn expr
      putStrLn $ show r
      P.return ()
{-
t :: IO ()
t = do
     conn <- getXConn
     I.debugX100 conn $ groupWith (\(view -> (n, d, i)) -> d) employees
-}
{-
test :: IO ()
test = do 
        conn <- getConn
        q <- I.debugPlan conn $ query
        putStrLn $ q    

employees :: Q [(Text, Text, Integer)]
employees = toQ [
    ("Simon",  "MS",   80)
  , ("Erik",   "MS",   90)
  , ("Phil",   "Ed",   40)
  , ("Gordon", "Ed",   45)
  , ("Paul",   "Yale", 60)
  ]
-}
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
