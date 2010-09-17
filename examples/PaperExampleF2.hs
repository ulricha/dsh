{-# LANGUAGE ViewPatterns, QuasiQuotes, TemplateHaskell, TransformListComp #-}
module PaperExampleF2 where

import qualified Ferry as Q    
import Ferry (Q, toQ, view, qc)
import Ferry.HSCompiler (fromQ)

import Database.HDBC
import Database.HDBC.PostgreSQL
import GHC.Exts (the)
import Data.List (nub)
import Ferry.Compiler
import Data.Text

getConn :: IO Connection
getConn = connectPostgreSQL "user = 'postgres' password = 'haskell98' host = 'localhost' dbname = 'ferry'"

type Facility = Text
type Cat      = Text
type Feature  = Text
type Meaning  = Text

facilities :: Q [(Cat, Facility)]
facilities = Q.table "Facilities"
               
features :: Q [(Facility, Feature)]
features = Q.table "Features"
          
meanings :: Q [(Feature, Meaning)]
meanings = Q.table "Meanings"
            
hasFeatures :: Q Text -> Q [Text] 
hasFeatures f = [$qc|feat | (fac,feat) <- features, fac Q.== f|]

means :: Q Text -> Q Text
means f = Q.head [$qc| mean | (feat,mean) <- meanings, feat `Q.eq` f |]

query :: Q [(Text , [Text ])] 
query = [$qc| Q.fromView (Q.the cat, Q.nub $ Q.concat $ Q.map (Q.map means . hasFeatures) fac) 
                        | (cat, fac) <- facilities, then group by cat |]
main :: IO ()
main = do
  conn <- getConn
  
  sqlDump <- readFile "PaperExampleData.sql"
  runRaw conn sqlDump
  
  result <- fromQ conn query
  print result