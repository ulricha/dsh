{-# LANGUAGE ViewPatterns, QuasiQuotes, TemplateHaskell #-}
module Test where
    
import Ferry (toQ, fromQ, Q (..), view, qc)
import qualified Ferry as Q
import Database.HDBC.Sqlite3
-- import qualified Ferry.Combinators

conn :: Connection
conn = undefined

test :: IO [Int]
test = fromQ conn $ Q.map (\(view -> (e,t)) -> e) $ toQ [(1,True), (3,False)]


ints :: Q [Int]
ints = toQ [1,2,3]

--test2 :: Q [Int]
--test2 = [$qc| x +y | x <- ints, toQ True, let y = 5 |]

test4 = [$qc| x | x <- ints, then Q.tail |]

main :: IO ()
main = do
  fromQ conn test4 >>= print