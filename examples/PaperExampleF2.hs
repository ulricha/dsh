{-# LANGUAGE ViewPatterns, QuasiQuotes, TemplateHaskell, TransformListComp #-}
module PaperExampleF2 where
    
import Ferry (toQ, fromQ, Q (..), view, qc)
import qualified Ferry as Q
import Database.HDBC.PostgreSQL
import GHC.Exts (the)
import Data.List (nub)

conn :: IO Connection
conn = connectPostgreSQL "user = 'postgres' password = 'haskell98' host = 'localhost' dbname = 'ferryDB'"

type Facility = String
type Cat      = String
type Feature  = String
type Meaning  = String

facilities :: Q [(Facility, Cat)]
facilities = Q.table "Facilities"
               
features :: Q [(Facility, Feature)]
features = Q.table "Features"
          
meanings :: Q [(Feature, Meaning)]
meanings = Q.table "Meanings"
            
-- Haskell version:

hasFeatures :: Q String -> Q [String] 
hasFeatures f = [$qc|feat | (fac,feat) <- features, Q.eq fac f|]

means :: Q String -> Q String
means f = Q.head [$qc| mean | (feat,mean) <- meanings, Q.eq feat f |]

-- Only need Q.nub combinator
query :: IO [(String , [String ])] 
query = do
         conn <- conn
         fromQ conn [$qc| Q.fromView (Q.the cat, Q.nub $ Q.concat $ Q.map (Q.map means . hasFeatures) fac) 
                        | (fac, cat) <- facilities, then group by cat |]

main :: IO ()
main = query >>= print