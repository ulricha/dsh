{-# LANGUAGE MonadComprehensions, RebindableSyntax, ViewPatterns #-}

module Main where

import qualified Prelude as P
import Database.DSH
import Database.DSH.Compiler

import Database.HDBC.PostgreSQL

ints :: Q [Integer]
ints = toQ [1 .. 10]

query1 :: Q [(Integer,Integer)]
query1 =  [ tuple (i1,i2)
          | i1 <- ints
          , i2 <- ints
          ]

query2 :: Q [(Integer,Integer)]
query2 =  [ tuple (i1,i2)
          | (view -> (i1,i2)) <- query1
          , i1 == i2
          ]

getConn :: IO Connection
getConn = connectPostgreSQL "user = 'giorgidz' password = '' host = 'localhost' dbname = 'giorgidz'"

runQ :: (Show a,QA a) => Q a -> IO ()
runQ q = getConn P.>>= \conn -> (fromQ conn q P.>>= P.print) P.>> disconnect conn

main :: IO ()
main = runQ ints P.>> runQ query1 P.>> runQ query2