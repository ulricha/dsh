-- This example was taken from the paper called "Comprehensive Comprehensions"
-- by Phil Wadler and Simon Peyton Jones

{-# LANGUAGE MonadComprehensions, RebindableSyntax, ViewPatterns #-}

module Main where

import qualified Prelude as P 
import Database.DSH
import Database.DSH.Compiler

import Database.HDBC.PostgreSQL

ints :: Q [Integer]
ints = toQ [1 .. 10]

query :: Q [(Integer,Integer)]
query = [ tuple (i1, i2)
        | i1 <- ints
        , i2 <- ints
        ]

getConn :: IO Connection
getConn = connectPostgreSQL "user = 'giorgidz' password = '' host = 'localhost' dbname = 'giorgidz'"

main :: IO ()
main = 
  getConn          P.>>= \conn ->
  fromQ conn query P.>>= P.print