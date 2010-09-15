{-# LANGUAGE ViewPatterns, QuasiQuotes, TemplateHaskell, TransformListComp #-}
module PaperExampleF2 where

import qualified Ferry as Q    
import Ferry (Q, toQ, view, qc)
import Ferry.Interpreter (fromQ)

import Database.HDBC.PostgreSQL
import GHC.Exts (the)
import Data.List (nub)
import Ferry.Compiler
import Data.Text

conn :: IO Connection
conn = connectPostgreSQL "user = 'postgres' password = 'haskell98' host = 'localhost' dbname = 'ferryDB'"

type Facility = Text
type Cat      = Text
type Feature  = Text
type Meaning  = Text

facilities :: Q [(Facility, Cat)]
facilities = Q.table "Facilities"
               
features :: Q [(Facility, Feature)]
features = Q.table "Features"
          
meanings :: Q [(Feature, Meaning)]
meanings = Q.table "Meanings"
            
-- Haskell version:

hasFeatures :: Q Text -> Q [Text] 
hasFeatures f = [$qc|feat | (fac,feat) <- features, fac Q.== f|]

means :: Q Text -> Q Text
means f = Q.head [$qc| mean | (feat,mean) <- meanings, feat `Q.eq` f |]

-- Only need Q.nub combinator
q2 :: Q [(Text , [Text ])] 
q2 = [$qc| Q.fromView (Q.the cat, Q.nub $ Q.concat $ Q.map (Q.map means . hasFeatures) fac) 
                        | (fac, cat) <- facilities, then group by cat |]

-- Only need Q.nub combinator
query :: IO [(Text , [Text ])] 
query = do
         conn <- conn
         fromQ conn [$qc| Q.fromView (Q.the cat, Q.nub $ Q.concat $ Q.map (Q.map means . hasFeatures) fac) 
                        | (fac, cat) <- facilities, then group by cat |]
squery :: IO [Text]
squery = do
            conn <- conn
            fromQ conn $ Q.tail [$qc| feat | (fac, feat) <- features|]

main2 :: IO ()
main2 = squery >>= print

main :: IO ()
main = query >>= print