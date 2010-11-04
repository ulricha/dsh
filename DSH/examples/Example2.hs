{-# LANGUAGE ViewPatterns, QuasiQuotes, TemplateHaskell #-}
module Test where

import Prelude ()
import Database.DSH
import Database.DSH.Interpreter

import Database.HDBC.PostgreSQL


conn :: Connection
conn = undefined

test :: IO [Integer]
test = fromQ conn $ map (\(view -> (e,t)) -> e) $ toQ [(1,True), (3,False)]


ints :: Q [Integer]
ints = toQ [1,2,3]

test2 :: Q [Integer]
test2 = [$qc| x + y | x <- ints, toQ True, let y = 5 |]

test4 = [$qc| x | x <- ints, then tail |]

test5 = [$qc| tuple (x,y,z) | x <- ints | y <- ints, z <- ints, y == z && y `eq` z |]

main :: IO ()
main = do
  fromQ conn test4 >>= print
  fromQ conn test2 >>= print
  fromQ conn test5 >>= print 