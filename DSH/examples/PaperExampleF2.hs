{-# LANGUAGE QuasiQuotes #-}
module PaperExampleF2 where

import Prelude ()
import Database.DSH
import Database.DSH.Compiler

import Database.HDBC.PostgreSQL

getConn :: IO Connection
getConn = connectPostgreSQL "user = 'postgres' password = 'haskell98' host = 'localhost' dbname = 'ferry'"

type Facility = Text
type Cat      = Text
type Feature  = Text
type Meaning  = Text

facilities :: Q [(Cat, Facility)]
facilities = table "Facilities"
               
features :: Q [(Facility, Feature)]
features = table "Features"
          
meanings :: Q [(Feature, Meaning)]
meanings = table "Meanings"
            
hasFeatures :: Q Text -> Q [Text] 
hasFeatures f = [$qc| feat | (fac,feat) <- features, fac == f |]

means :: Q Text -> Q Text
means f = head [$qc| mean | (feat,mean) <- meanings, feat == f |]

query :: Q [(Text , [Text ])] 
query = [$qc| fromView (the cat, nub $ concat $ map (map means . hasFeatures) fac) 
                       | (cat, fac) <- facilities, then group by cat |]
main :: IO ()
main = do
  conn <- getConn
  
  sqlDump <- readFile "PaperExampleData.sql"
  runRaw conn sqlDump
  
  result <- fromQ conn query
  print result