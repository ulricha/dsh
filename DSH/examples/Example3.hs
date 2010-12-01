{-# LANGUAGE QuasiQuotes, ViewPatterns #-}

module Main where

import Prelude ()

import Database.DSH
import Database.DSH.Interpreter

import Database.HDBC.PostgreSQL

q1 :: Q [(Bool,Char,Integer,Double,Text)]
q1 = tableCSV "Example3.csv"

conn :: Connection
conn = undefined

main :: IO ()
main = do
  fromQ conn q1 >>= print
