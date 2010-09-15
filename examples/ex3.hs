{-# LANGUAGE ViewPatterns, QuasiQuotes, TemplateHaskell #-}
module Test where

import qualified Ferry as Q    
import Ferry (Q,toQ,view,fromView,table,qc)
import Ferry.Interpreter (fromQ)

import Database.HDBC.PostgreSQL


conn :: Connection
conn = undefined

test :: IO [Integer]
test = fromQ conn $ Q.map (\(view -> (e,t)) -> e) $ toQ [(1,True), (3,False)]


ints :: Q [Integer]
ints = toQ [1,2,3]

test2 :: Q [Integer]
test2 = [$qc| x + y | x <- ints, toQ True, let y = 5 |]

test4 = [$qc| x | x <- ints, then Q.tail |]

test5 = [$qc| Q.fromView (x,y,z) | x <- ints | y <- ints, z <- ints, y Q.== z Q.&& y `Q.eq` z |]

main :: IO ()
main = do
  fromQ conn test4 >>= print
  fromQ conn test2 >>= print
  fromQ conn test5 >>= print 