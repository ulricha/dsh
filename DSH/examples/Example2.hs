-- This example was taken from the paper called "Comprehensive Comprehensions"
-- by Phil Wadler and Simon Peyton Jones

{-# LANGUAGE MonadComprehensions, TransformListComp, ViewPatterns, OverloadedStrings #-}

module Main where

import Prelude ()
import Database.DSH
import Database.DSH.Compiler

import Database.HDBC.PostgreSQL

employees :: Q L (Q S (Q S Text, Q S Text, Q S Integer))
employees = toQ [
    ("Simon",  "MS",   80)
  , ("Erik",   "MS",   90)
  , ("Phil",   "Ed",   40)
  , ("Gordon", "Ed",   45)
  , ("Paul",   "Yale", 60)
  ]

query :: Q L (Q S (Q S Text, Q S Integer))
query = [ tuple (the dept, sum salary)
        | (view -> (name, dept, salary)) <- employees
        , then group by dept
        , then sortWith by (sum salary)
        , then take 5
        ]

getConn :: IO Connection
getConn = connectPostgreSQL "user = 'giorgidz' password = '' host = 'localhost' dbname = 'giorgidz'"

main :: IO ()
main = do
  conn   <- getConn
  result <- fromQ conn query
  print result