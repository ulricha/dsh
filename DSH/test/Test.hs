module Test where

import qualified Database.DSH as Q
import qualified Database.DSH.Flattening as I

import qualified Database.HDBC as HDBC
import Database.HDBC.PostgreSQL

getConn :: IO Connection
getConn = connectPostgreSQL "user = 'postgres' password = 'haskell98' host = 'localhost' dbname = 'ferry'"

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