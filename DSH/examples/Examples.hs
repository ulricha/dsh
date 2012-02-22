-- This example was taken from the paper called "Comprehensive Comprehensions"
-- by Phil Wadler and Simon Peyton Jones

{-# LANGUAGE QuasiQuotes, OverloadedStrings, MonadComprehensions, TransformListComp, ViewPatterns #-}

module Main where

import Prelude ()
import Database.DSH
import Database.DSH.Flattening

import Database.HDBC.PostgreSQL

d1 :: Q [(Integer, Integer)]
d1 = toQ $ [(1, 10), (2, 20), (3, 30)]

d2 :: Q [Integer]
d2 = toQ [1..100]

d3 :: Q [(Integer, Bool)]
d3 = toQ [(1, True), (2, True), (3,False), (4,True)]

query3 :: Q [(Integer, (Integer, Integer))]
query3 = concat $ map (\x -> cond (snd x) (singleton $ tuple (fst x, tuple (fst x + 1, fst x - 1))) empty) d3


query :: Q Integer
query = sum $ map (\(view -> (x, y)) -> x + y) d1


query2 :: Q [[Integer]]
query2 = groupWith (<=50) d2

main :: IO ()
main = do
  debugX100 undefined query3
