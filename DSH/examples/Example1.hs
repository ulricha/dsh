{-# LANGUAGE QuasiQuotes, ViewPatterns #-}

module Main where

import Prelude ()

import Database.DSH
import Database.DSH.Interpreter

import Database.HDBC.PostgreSQL

employees :: Q [([Char], [Char], Integer)]
employees = toQ [
    ("Simon",  "MS",   80)
  , ("Erik",   "MS",   90)
  , ("Phil",   "Ed",   40)
  , ("Gordon", "Ed",   45)
  , ("Paul",   "Yale", 60)
  ]

q1 = map (\(view->(n,_,s)) -> fromView (s,n)) employees
q2 = sortWith id q1
q3 = append q1 q2
q4 = groupWith fst q1
q5 = map (+ 42) (toQ [1 .. 10 :: Integer])

q6 = [$qc| e | e <- (toQ "foo"), let a = e |]

q7 :: Q [(String, Integer)]
q7 = [$qc| fromView (the dept, sum salary)
         | (name, dept, salary) <- employees
         , then group by dept
         , then sortWith by (sum salary)
         , then take 5 |]

conn :: Connection
conn = undefined

main :: IO ()
main = do
  fromQ conn q1 >>= print
  fromQ conn q2 >>= print
  fromQ conn q3 >>= print
  fromQ conn q4 >>= print
  fromQ conn q5 >>= print
  fromQ conn q6 >>= print
  fromQ conn q7 >>= print