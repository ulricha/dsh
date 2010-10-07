module Main where

import qualified Ferry as Q
-- import qualified Ferry.HSCompiler as C
import qualified Ferry.Interpreter as I

-- import Database.HDBC (IConnection, disconnect)
import Database.HDBC.PostgreSQL

import Test.QuickCheck
import Test.QuickCheck.Monadic

import Data.List
import GHC.Exts

-- getConn :: IO Connection
-- getConn = connectPostgreSQL "user = 'postgres' password = 'haskell98' host = 'localhost' dbname = 'ferry'"

main :: IO ()
main = do
    putStrLn "Running DSH prelude tests"
    putStrLn "-------------------------"
    putStr "unit:           "
    quickCheck prop_unit

    putStrLn ""
    putStrLn "Equality & Ordering"
    putStrLn "-------------------------"
    putStr "&&:             "
    quickCheck prop_infix_and
    putStr "||:             "
    quickCheck prop_infix_or
    putStr "not:            "
    quickCheck prop_not
    putStr "eq:             "
    quickCheck prop_eq_int
    putStr "neq:            "
    quickCheck prop_neq_int
    putStr "lt:             "
    quickCheck prop_lt
    putStr "lte:            "
    quickCheck prop_lte
    putStr "gt:             "
    quickCheck prop_gt
    putStr "gte:            "
    quickCheck prop_gte

    putStrLn ""
    putStrLn "Lists"
    putStrLn "-------------------------"
    putStr "head:           "
    quickCheck prop_head
    putStr "tail:           "
    quickCheck prop_tail
    putStr "cons:           "
    quickCheck prop_cons
    putStr "snoc:           "
    quickCheck prop_snoc
    putStr "take:           "
    quickCheck prop_take
    putStr "drop:           "
    quickCheck prop_drop
    putStr "map_id:         "
    quickCheck prop_map_id
    putStr "filter_True:    "
    quickCheck prop_filter_True
    putStr "the:            "
    quickCheck prop_the
    putStr "last:           "
    quickCheck prop_last
    putStr "init:           "
    quickCheck prop_init
    putStr "null:           "
    quickCheck prop_null
    putStr "length:         "
    quickCheck prop_length
    putStr "index:          "
    quickCheck prop_index
    putStr "reverse:        "
    quickCheck prop_reverse
    putStr "append:         "
    quickCheck prop_append
    putStr "groupWith_id:   "
    quickCheck prop_groupWith_id
    putStr "sortWith_id:    "
    quickCheck prop_sortWith_id

    putStrLn ""
    putStrLn "Special folds"
    putStrLn "-------------------------"
    putStr "and:            "
    quickCheck prop_and
    putStr "or:             "
    quickCheck prop_or
    putStr "any_zero:       "
    quickCheck prop_any_zero
    putStr "all_zero:       "
    quickCheck prop_all_zero
    putStr "sum:            "
    quickCheck prop_sum
    putStr "product:        "
    quickCheck prop_product
    putStr "concat:         "
    quickCheck prop_concat
    putStr "concatMap:      "
    quickCheck prop_concatMap
    putStr "maximum:        "
    quickCheck prop_maximum
    putStr "minimum:        "
    quickCheck prop_minimum
    putStr "replicate:      "
    quickCheck prop_replicate

    putStrLn ""
    putStrLn "Sublists"
    putStrLn "-------------------------"
    putStr "splitAt:        "
    quickCheck prop_splitAt
    putStr "takeWhile:      "
    quickCheck prop_takeWhile
    putStr "dropWhile:      "
    quickCheck prop_dropWhile
    putStr "span:           "
    quickCheck prop_span
    putStr "break:          "
    quickCheck prop_break

    putStrLn ""
    putStrLn "Searching lists"
    putStrLn "-------------------------"
    putStr "elem:           "
    quickCheck prop_elem
    putStr "notElem:        "
    quickCheck prop_notElem

    putStrLn ""
    putStrLn "Zipping and unzipping lists"
    putStrLn "-------------------------"
    putStr "zip:            "
    quickCheck prop_zip
    putStr "zipWith_plus:   "
    quickCheck prop_zipWith_plus
    putStr "unzip:          "
    quickCheck prop_unzip

    putStrLn ""
    putStrLn "Set operations"
    putStrLn "-------------------------"
    putStr "nub:            "
    quickCheck prop_nub

    putStrLn ""
    putStrLn "Tuple projection functions"
    putStrLn "-------------------------"
    putStr "fst:            "
    quickCheck prop_fst
    putStr "snd:            "
    quickCheck prop_snd


runTest :: (Eq b, Q.QA a, Q.QA b)
        => (Q.Q a -> Q.Q b)
        -> (a -> b)
        -> a
        -> Property
runTest q f arg = monadicIO $ do
    -- c <- run $ getConn
    -- db <- run $ C.fromQ c $ q (Q.toQ arg) 
    it <- run $ I.fromQ (undefined :: Connection) $ q (Q.toQ arg)
    -- run $ disconnect c
    let hs = f arg
    assert (it == hs) -- (db == hs && it == hs)

-- | Test if the list isn't empty
testNotNull :: (Eq b, Q.QA a, Q.QA b)
            => (Q.Q [a] -> Q.Q b)
            -> ([a] -> b)
            -> [a]
            -> Property
testNotNull q f arg = not (null arg) ==> runTest q f arg


uncurry_Q :: (Q.QA a, Q.QA b) => (Q.Q a -> Q.Q b -> Q.Q c) -> Q.Q (a,b) -> Q.Q c
uncurry_Q q = uncurry q . Q.view

-- Kinda pointless, but meh... :)
prop_unit :: () -> Property
prop_unit = runTest (const $ Q.unit) id

--------------------------------------------------------------------------------
-- Equality & Ordering

prop_infix_and :: (Bool,Bool) -> Property
prop_infix_and = runTest (uncurry_Q (Q.&&)) (uncurry (&&))

prop_infix_or :: (Bool,Bool) -> Property
prop_infix_or = runTest (uncurry_Q (Q.||)) (uncurry (||))

prop_not :: Bool -> Property
prop_not = runTest Q.not not

prop_eq :: (Eq a, Q.QA a) => (a,a) -> Property
prop_eq = runTest (\q -> Q.fst q Q.== Q.snd q) (\(a,b) -> a == b)

prop_eq_int :: (Integer,Integer) -> Property
prop_eq_int = prop_eq

prop_neq :: (Eq a, Q.QA a) => (a,a) -> Property
prop_neq = runTest (uncurry_Q (Q./=)) (\(a,b) -> a /= b)

prop_neq_int :: (Integer,Integer) -> Property
prop_neq_int = prop_eq

prop_lt :: (Integer, Integer) -> Property
prop_lt = runTest (uncurry_Q (Q.<)) (uncurry (<))

prop_lte :: (Integer, Integer) -> Property
prop_lte = runTest (uncurry_Q (Q.<=)) (uncurry (<=))

prop_gt :: (Integer, Integer) -> Property
prop_gt = runTest (uncurry_Q (Q.>)) (uncurry (>))

prop_gte :: (Integer, Integer) -> Property
prop_gte = runTest (uncurry_Q (Q.>=)) (uncurry (>=))


--------------------------------------------------------------------------------
-- Lists

prop_cons :: (Integer, [Integer]) -> Property
prop_cons = runTest (uncurry_Q (Q.<|)) (uncurry (:))

prop_snoc :: ([Integer], Integer) -> Property
prop_snoc = runTest (uncurry_Q (Q.|>)) (\(a,b) -> a ++ [b])

prop_singleton :: Integer -> Property
prop_singleton = runTest Q.singleton (\x -> [x])


-- head, tail, last, init, the and index may fail:

prop_head  :: [Integer] -> Property
prop_head  = testNotNull Q.head head

prop_tail  :: [Integer] -> Property
prop_tail  = testNotNull Q.tail tail

prop_last  :: [Integer] -> Property
prop_last  = testNotNull Q.last last

prop_init  :: [Integer] -> Property
prop_init  = testNotNull Q.init init

prop_the   :: [Integer] -> Property
prop_the l =
        allEqual l
    ==> runTest Q.the the l
  where
    allEqual []     = False
    allEqual (x:xs) = all (x ==) xs

prop_index :: ([Integer], Integer)  -> Property
prop_index (l, i) =
        i > 0 && i < fromIntegral (length l)
    ==> runTest (uncurry_Q (Q.!!))
                (\(a,b) -> a !! fromIntegral b)
                (l, i)


prop_take :: (Integer, [Integer]) -> Property
prop_take = runTest (uncurry_Q Q.take) (\(n,l) -> take (fromIntegral n) l)

prop_drop :: (Integer, [Integer]) -> Property
prop_drop = runTest (uncurry_Q Q.drop) (\(n,l) -> drop (fromIntegral n) l)

-- | Map "id" over the list
prop_map_id :: [Integer] -> Property
prop_map_id = runTest (Q.map id) (map id)

prop_append :: ([Integer], [Integer]) -> Property
prop_append = runTest (uncurry_Q Q.append) (\(a,b) -> a ++ b)

-- | filter "const True"
prop_filter_True :: [Integer] -> Property
prop_filter_True = runTest (Q.filter (const $ Q.toQ True)) (filter $ const True)

prop_groupWith_id :: [Integer] -> Property
prop_groupWith_id = runTest (Q.groupWith id) (groupWith id)

prop_sortWith_id  :: [Integer] -> Property
prop_sortWith_id = runTest (Q.sortWith id) (sortWith id)

prop_null :: [Integer] -> Property
prop_null = runTest Q.null null

prop_length :: [Integer] -> Property
prop_length = runTest Q.length (fromIntegral . length)

prop_reverse :: [Integer] -> Property
prop_reverse = runTest Q.reverse reverse


--------------------------------------------------------------------------------
-- Special folds

prop_and :: [Bool] -> Property
prop_and = runTest Q.and and

prop_or :: [Bool] -> Property
prop_or = runTest Q.or or

prop_any_zero :: [Integer] -> Property
prop_any_zero = runTest (Q.any (Q.== 0)) (any (== 0))

prop_all_zero :: [Integer] -> Property
prop_all_zero = runTest (Q.all (Q.== 0)) (all (== 0))

prop_sum :: [Integer] -> Property
prop_sum = runTest Q.sum sum

prop_product :: [Integer] -> Property
prop_product = runTest Q.product product

prop_concat :: [[Integer]] -> Property
prop_concat = runTest Q.concat concat

prop_concatMap :: [Integer] -> Property
prop_concatMap = runTest (Q.concatMap Q.singleton) (concatMap (\a -> [a]))


-- maximum & minimum can fail:

prop_maximum :: [Integer] -> Property
prop_maximum = testNotNull Q.maximum maximum

prop_minimum :: [Integer] -> Property
prop_minimum = testNotNull Q.minimum minimum


prop_replicate :: (Integer, [Integer]) -> Property
prop_replicate = runTest (uncurry_Q Q.replicate) (\(a,b) -> replicate (fromIntegral a) b)


--------------------------------------------------------------------------------
-- Sublists

prop_splitAt :: (Integer, [Integer]) -> Property
prop_splitAt = runTest (uncurry_Q Q.splitAt) (\(a,b) -> splitAt (fromIntegral a) b)

prop_takeWhile :: (Integer, [Integer]) -> Property
prop_takeWhile = runTest (uncurry_Q $ Q.takeWhile . (Q.==))
                         (uncurry   $   takeWhile . (==) . fromIntegral)

prop_dropWhile :: (Integer, [Integer]) -> Property
prop_dropWhile = runTest (uncurry_Q $ Q.dropWhile . (Q.==))
                         (uncurry   $   dropWhile . (==) . fromIntegral)

prop_span :: (Integer, [Integer]) -> Property
prop_span = runTest (uncurry_Q $ Q.span . (Q.==))
                    (uncurry   $   span . (==) . fromIntegral)

prop_break :: (Integer, [Integer]) -> Property
prop_break = runTest (uncurry_Q $ Q.break . (Q.==))
                     (uncurry   $   break . (==) . fromIntegral)


--------------------------------------------------------------------------------
-- Searching lists

prop_elem :: (Integer, [Integer]) -> Property
prop_elem = runTest (uncurry_Q Q.elem) (uncurry elem)

prop_notElem :: (Integer, [Integer]) -> Property
prop_notElem = runTest (uncurry_Q Q.notElem) (uncurry notElem)


--------------------------------------------------------------------------------
-- Zipping and unzipping lists

prop_zip :: ([Integer], [Integer]) -> Property
prop_zip = runTest (uncurry_Q Q.zip) (uncurry zip)

prop_zipWith_plus :: ([Integer], [Integer]) -> Property
prop_zipWith_plus = runTest (uncurry_Q $ Q.zipWith (+)) (uncurry $ zipWith (+))

prop_unzip :: [(Integer, Integer)] -> Property
prop_unzip = runTest Q.unzip unzip


--------------------------------------------------------------------------------
-- Set operations

prop_nub :: [Integer] -> Property
prop_nub = runTest Q.nub nub


--------------------------------------------------------------------------------
-- Tuple projection functions

prop_fst :: (Integer, Integer) -> Property
prop_fst = runTest Q.fst fst

prop_snd :: (Integer, Integer) -> Property
prop_snd = runTest Q.snd snd
