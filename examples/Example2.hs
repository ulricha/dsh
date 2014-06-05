-- This example was taken from the paper called "Comprehensive Comprehensions"
-- by Phil Wadler and Simon Peyton Jones

{-# LANGUAGE QuasiQuotes, OverloadedStrings #-}

module Main where

import Prelude ()
import Database.DSH
import Database.DSH.Compiler

import Database.HDBC.PostgreSQL

employees :: Q [(Text, Text, Integer)]
employees = toQ [
    ("Simon",  "MS",   80)
  , ("Erik",   "MS",   90)
  , ("Phil",   "Ed",   40)
  , ("Gordon", "Ed",   45)
  , ("Paul",   "Yale", 60)
  ]

query :: Q [(Text, Integer)]
query = [$qc| tuple (the dept, sum salary)
            | (name, dept, salary) <- employees
            , then group by dept
            , then sortWith by (sum salary)
            , then take 5 |]

getConn :: IO Connection
getConn = connectPostgreSQL "user = 'postgres' password = 'haskell98' host = 'localhost' dbname = 'ferry'"

main :: IO ()
main = do
  conn   <- getConn
  result <- debugPlan conn query
  putStrLn result