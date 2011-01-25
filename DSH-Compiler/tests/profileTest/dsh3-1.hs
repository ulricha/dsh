{-# LANGUAGE QuasiQuotes #-}
module Main where

import Prelude ()
import qualified Prelude as P (length, last, take, map, snd)
import Database.DSH
import Database.DSH.Compiler
-- import Database.DSH.Interpreter


import Database.HDBC.PostgreSQL

getConn :: IO Connection
getConn = connectPostgreSQL "user = 'postgres' password = 'haskell98' host = 'localhost' dbname = 'ferryBig'"

type Facility = Text
type Cat      = Text
type Feature  = Text
type Meaning  = Text

facilities :: Q [(Cat, Facility)]
facilities = table "facilities"
               
features :: Q [(Facility, Feature)]
features = table "features"
          
meanings :: Q [(Feature, Meaning)]
meanings = table "meanings"
            
-- hasFeatures :: Q Text -> Q [Text] 
-- hasFeatures f = [$qc| feat |  fac == f |]

descrFacility :: Q Facility -> Q [Meaning]
descrFacility f =  [$qc| mean | (feat,mean) <- meanings, 
                                (fac,feat1) <- features, 
                                feat == feat1 && fac == f|]

{-
descrFacility :: String -> [String]
descrFacility f =  [mean |  (feat,mean) <- meanings, 
                            (fac,feat1) <- features, 
                            feat == feat1 && fac == f]
-}

query :: Q [(Text , [Text])] 
query = [$qc| tuple (the cat, nub $ concatMap descrFacility fac) 
            | (cat, fac) <- facilities, then group by cat |]


{-
query :: [(String , [String])] 
query =  [  (the cat, nub (concatMap descrFacility fac)) 
         |  (fac, cat) <- facilities, then group by cat ]
-}

-- -- hasFeatures :: Q String -> Q [String]
-- hasFeatures f = map snd (filter (\a -> fst a == f) features)
-- 
-- -- means :: Q String -> Q String
-- means f = head (map snd (filter (\a -> fst a == f) meanings))
-- 
-- -- query :: IO [(String , [String ])] 
-- query = map (\fcs -> let 
--                         v1 = the (map snd fcs)
--                         v2 = map (\fc -> concatMap (\ff -> map snd (filter (\m -> fst m == snd ff && fst ff == fst fc) meanings)
--                                         )
--                                         features
--                             )
--                             fcs
--                      in  tuple (v1,nub (concat v2))
--       )
--       (groupWith snd facilities)




myQuery = do
             conn <- getConn
             result <- fromQ conn query
             --result <- debugFromQ conn query
             print $ P.length result
             return result

-- main :: IO ()
-- main = do
--   conn <- getConn
--   
--   -- sqlDump <- readFile "PaperExampleData.sql"
--   -- runRaw conn sqlDump
--   
--   result <- fromQ conn query
--   print result

main = myQuery