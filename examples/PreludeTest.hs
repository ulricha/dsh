module PreludeTest where

import qualified Ferry as Q
import qualified Ferry.HSCompiler as C
import qualified Ferry.Interpreter as I

import Database.HDBC (IConnection, disconnect)
import Database.HDBC.PostgreSQL

-- import Data.Time
-- import qualified Data.Text as Text
-- import Data.List
import Test.QuickCheck
import Test.QuickCheck.Monadic

getConn :: IO Connection
getConn = connectPostgreSQL "user = 'postgres' password = 'haskell98' host = 'localhost' dbname = 'ferry'"

main :: IO ()
main = do
    putStrLn "Running DSH prelude tests"
    putStrLn "-------------------------"
    quickCheck prop_fst
    quickCheck prop_snd
    quickCheck prop_and
    quickCheck prop_or
    quickCheck prop_not

    putStrLn ""
    putStrLn "Equality & Ordering"
    putStrLn "-------------------------"
    quickCheck prop_eq_int
    quickCheck prop_neq_int
    quickCheck prop_lt
    quickCheck prop_lte
    quickCheck prop_gt
    quickCheck prop_gte

    putStrLn ""
    putStrLn "Lists"
    putStrLn "-------------------------"
    quickCheck prop_cons
    -- quickCheck prop_snoc
    quickCheck prop_head
    quickCheck prop_tail
    quickCheck prop_take
    quickCheck prop_drop
    quickCheck prop_map_id
    quickCheck prop_filter_True

runTest :: (Eq b, Q.QA a, Q.QA b) => (Q.Q a -> Q.Q b) -> (a -> b) -> a -> Property
runTest q f arg = monadicIO $ do
                          c <- run $ getConn
                          db <- run $ C.fromQ c $ q (Q.toQ arg) 
                          it <- run $ I.fromQ c $ q (Q.toQ arg)
                          run $ disconnect c
                          let hs = f arg
                          assert (db == hs && it == hs)

prop_fst :: (Integer, Integer) -> Property
prop_fst = runTest Q.fst fst

prop_snd :: (Integer, Integer) -> Property
prop_snd = runTest Q.snd snd

prop_and :: [Bool] -> Property
prop_and = runTest Q.and and

prop_or :: [Bool] -> Property
prop_or = runTest Q.or or

prop_not :: Bool -> Property
prop_not = runTest Q.not not

--------------------------------------------------------------------------------
-- Equality & Ordering

prop_eq :: (Eq a, Q.QA a) => (a,a) -> Property
prop_eq = runTest (\q -> Q.fst q Q.== Q.snd q) (\(a,b) -> a == b)

prop_eq_int :: (Integer,Integer) -> Property
prop_eq_int = prop_eq

-- prop_eq_char :: (Char,Char) -> Property
-- prop_eq_char = prop_eq

-- prop_eq_utctime :: (UTCTime, UTCTime) -> Property
-- prop_eq_utctime = prop_eq

-- prop_eq_text :: (Text, Text) -> Property
-- prop_eq_text = prop_eq

prop_neq :: (Eq a, Q.QA a) => (a,a) -> Property
prop_neq = runTest (\q -> Q.fst q Q./= Q.snd q) (\(a,b) -> a /= b)

prop_neq_int :: (Integer,Integer) -> Property
prop_neq_int = prop_eq

-- prop_neq_char :: (Char,Char) -> Property
-- prop_neq_char = prop_eq

-- prop_neq_utctime :: (UTCTime, UTCTime) -> Property
-- prop_neq_utctime = prop_eq

-- prop_neq_text :: (Text, Text) -> Property
-- prop_neq_text = prop_eq


prop_lt :: (Integer, Integer) -> Property
prop_lt = runTest (\q -> Q.fst q Q.< Q.snd q) (\(a,b) -> a < b)

prop_lte :: (Integer, Integer) -> Property
prop_lte = runTest (\q -> Q.fst q Q.<= Q.snd q) (\(a,b) -> a <= b)

prop_gt :: (Integer, Integer) -> Property
prop_gt = runTest (\q -> Q.fst q Q.> Q.snd q) (\(a,b) -> a > b)

prop_gte :: (Integer, Integer) -> Property
prop_gte = runTest (\q -> Q.fst q Q.>= Q.snd q) (\(a,b) -> a >= b)


--------------------------------------------------------------------------------
-- Lists

prop_cons :: (Integer, [Integer]) -> Property
prop_cons = runTest (\q -> Q.fst q Q.<| Q.snd q) (\(a,b) -> a : b)

prop_snoc :: ([Integer], Integer) -> Property
prop_snoc = runTest (\q -> Q.fst q Q.|> Q.snd q) (\(a,b) -> a ++ [b])

prop_singleton :: Integer -> Property
prop_singleton = runTest Q.singleton (\x -> [x])


prop_head :: [Integer] -> Property
prop_head = runTest Q.head head

prop_tail :: [Integer] -> Property
prop_tail = runTest Q.tail tail

prop_take :: (Integer, [Integer]) -> Property
prop_take = runTest (\q -> Q.take (Q.fst q) (Q.snd q)) (\(n,l) -> take (fromIntegral n) l)

prop_drop :: (Integer, [Integer]) -> Property
prop_drop = runTest (\q -> Q.drop (Q.fst q) (Q.snd q)) (\(n,l) -> drop (fromIntegral n) l)

-- | Map "id" over the list
prop_map_id :: [Integer] -> Property
prop_map_id = runTest (Q.map id) (map id)

prop_append :: ([Integer], [Integer]) -> Property
prop_append = runTest (\q -> Q.append (Q.fst q) (Q.snd q)) (\(a,b) -> a ++ b)

-- | filter "const True"
prop_filter_True :: [Integer] -> Property
prop_filter_True = runTest (Q.filter (const $ Q.toQ True)) (filter $ const True)
