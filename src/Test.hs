{-# LANGUAGE ViewPatterns, QuasiQuotes, TemplateHaskell #-}
module Test where
    
import Ferry (toQ, fromQ, Q (..), view, qc, rw)
import qualified Ferry as Q
import Database.HDBC.Sqlite3
import qualified Ferry.Combinators
import qualified Ferry.Class

conn :: Connection
conn = undefined

test :: IO [Int]
test = fromQ conn $ Q.map (\(view -> (e,t)) -> e) $ toQ [(1,True), (3,False)]


ints :: Q [Int]
ints = toQ [1,2,3]

--test2 :: Q [Int]
test2 = [$qc| x | x <- ints, x == x |]