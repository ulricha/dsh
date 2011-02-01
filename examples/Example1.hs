-- This module is part of the DSH-Compiler package and serves as an example on
-- howto use DSH. It is accompanied by a file ExampleData.sql that contains
-- SQL instructions to setup the database that is used by this example.

-- Quasiquoting has to be enabled to support the list comprehension syntax
{-# LANGUAGE QuasiQuotes #-}

module Main where

-- We hide everything in the prelude as DSH exposes a lot of same combinators.
-- In general we recommend to import the module Database.DSH module qualified.
-- The Database.DSH.Compiler module has to be imported seperately this module
-- contains the machinery necessary to execute the query. This module is part
-- of the DSH-Compiler package, the other module (Database.DSH) is part of
-- DSH-Core. We provide the modules in separate packages so that different
-- backend can be made and used for the DSH query facility.

import Prelude () 
import Database.DSH
import Database.DSH.Compiler

-- For our example we use postgresql, any database will do as long it can be
-- approached through HDBC.
import Database.HDBC.PostgreSQL

-- Setup the connection string. In order for this to work you must provide a
-- username, password, host and database name.
getConn :: IO Connection
getConn = connectPostgreSQL "user = 'postgres' password = 'haskell98' host = 'localhost' dbname = 'ferry'"

-- DSH uses Text instead of string for strings, as a string will be treated as a
-- list of characters.
type Facility = Text
type Cat      = Text
type Feature  = Text
type Meaning  = Text

-- Declare the database tables, note that you *MUST* declare all columns
-- present in a table. And all columns must be in the same order as they are
-- declared in the database. During compilation the types of the columns will
-- be checked against the provided haskell types. When possible the types of
-- columns will be inferred, if they cannot be fully inferred the user has to
-- provide explicit types!

facilities :: Q [(Cat, Facility)]
facilities = table "facilities"
               
features :: Q [(Facility, Feature)]
features = table "features"
          
meanings :: Q [(Feature, Meaning)]
meanings = table "meanings"
            
-- Helper function for the query.
-- Despite the different braces for the comprehension the comprehension body
-- works as normal
descrFacility :: Q Facility -> Q [Meaning]
descrFacility f =  [$qc| mean | (feat,mean) <- meanings, 
                                (fac,feat1) <- features, 
                                feat == feat1 && fac == f|]

-- Main query, use the helper function
query :: Q [(Text , [Text])] 
query = [$qc| tuple (the cat, nub $ concatMap descrFacility fac) 
            | (cat, fac) <- facilities, then group by cat |]


-- Execute the query
main :: IO ()
main = do
  conn   <- getConn           -- Get a connection
  result <- fromQ conn query  -- Execute the query using fromQ
  print result