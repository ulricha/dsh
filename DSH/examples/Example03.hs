{-# LANGUAGE DeriveGeneric, FlexibleInstances, MultiParamTypeClasses #-}
module Main where

import qualified Prelude as P
import GHC.Generics

import Database.DSH
import Database.DSH.Compiler

import Database.HDBC.PostgreSQL

data Foo = A Integer Integer Integer Integer | B | C | D
           deriving (Eq, Ord, Show, Generic)

instance QA Foo where
instance (QA r) => Case Foo r where

getConn :: IO Connection
getConn = connectPostgreSQL "user = 'giorgidz' password = '' host = 'localhost' dbname = 'giorgidz'"

runQ :: (Show a, QA a) => Q a -> IO ()
runQ q = getConn P.>>= \conn -> (fromQ conn q P.>>= P.print) P.>> disconnect conn

main :: IO ()
main = runQ (toQ (A 1 2 3 4))
  -- runQ (toQ (B))
  -- (runQ (gCurry ((flip caseOf) (toQ D)) (const (toQ 'a')) (const (toQ 'b')) (const (toQ 'c')) (const (toQ 'd'))))