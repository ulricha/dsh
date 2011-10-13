{-# LANGUAGE TemplateHaskell, FlexibleInstances, MultiParamTypeClasses #-}

module Main where

import qualified Prelude as P
import Database.DSH

import Database.HDBC.PostgreSQL
          
$(generateDatabaseRecordInstances (connectPostgreSQL "user = 'giorgidz' password = '' host = 'localhost' dbname = 'giorgidz'"))
$(generateTableDeclarations       (connectPostgreSQL "user = 'giorgidz' password = '' host = 'localhost' dbname = 'giorgidz'"))

main :: IO ()
main = P.return ()