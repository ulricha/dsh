{-# OPTIONS_GHC -fno-warn-orphans #-}

module Main where

import qualified Database.DSH as Q
import Database.DSH (Q, QA)

-- import Database.DSH.Interpreter (fromQ)
import Database.DSH.Compiler (fromQ)

import qualified Database.HDBC as HDBC
import Database.HDBC.PostgreSQL

import Test.QuickCheck
import Test.QuickCheck.Monadic

import Data.List
import GHC.Exts

import Data.Text (Text)
import qualified Data.Text as Text

import Data.Char

instance Arbitrary Text where
  arbitrary = fmap Text.pack arbitrary

getConn :: IO Connection
getConn = connectPostgreSQL "user = 'postgres' password = 'haskell98' host = 'localhost' dbname = 'ferry'"

qc:: Testable prop => prop -> IO ()
qc = quickCheckWith stdArgs{maxSuccess = 20, maxSize = 10}

main :: IO ()
main = do
    putStrLn "Running DSH prelude tests"
    putStrLn "-------------------------"
    putStr "unit:           "
    qc prop_unit
    putStr "Bool:           "
    qc prop_bool
    putStr "Char:           "
    qc prop_char
    putStr "Text:           "
    qc prop_text
    putStr "Integer:        "
    qc prop_integer
    putStr "Double:         "
    qc prop_double

    putStrLn ""
    putStrLn "Equality & Ordering"
    putStrLn "-------------------------"
    putStr "&&:             "
    qc prop_infix_and
    putStr "||:             "
    qc prop_infix_or
    putStr "not:            "
    qc prop_not
    putStr "eq:             "
    qc prop_eq_int
    putStr "neq:            "
    qc prop_neq_int
    putStr "lt:             "
    qc prop_lt
    putStr "lte:            "
    qc prop_lte
    putStr "gt:             "
    qc prop_gt
    putStr "gte:            "
    qc prop_gte
    putStr "min_integer:    "
    qc prop_min_integer
    putStr "min_double:     "
    qc prop_min_double
    putStr "max_integer:    "
    qc prop_max_integer
    putStr "max_double:     "
    qc prop_max_double

    putStrLn ""
    putStrLn "Tuple projection functions"
    putStrLn "-------------------------"
    putStr "fst:            "
    qc prop_fst
    putStr "snd:            "
    qc prop_snd

    putStrLn ""
    putStrLn "Conditionals:"
    putStrLn "-------------------------"
    putStr "cond:           "
    qc prop_cond

    putStrLn ""
    putStrLn "Numerical operations:"
    putStrLn "-------------------------"
    putStr "add_integer:    "
    qc prop_add_integer
    putStr "add_double:     "
    qc prop_add_double
    putStr "mul_integer:    "
    qc prop_mul_integer
    putStr "mul_double:     "
    qc prop_mul_double
    putStr "div_double:     "
    qc prop_div_double
    putStr "integer_to_double: "
    qc prop_integer_to_double    
    putStr "abs_integer:    "
    qc prop_abs_integer
    putStr "abs_double:     "
    qc prop_abs_double
    putStr "signum_integer: "
    qc prop_signum_integer
    putStr "signum_double:  "
    qc prop_signum_double
    putStr "negate_integer: "
    qc prop_negate_integer
    putStr "negate_double:  "
    qc prop_negate_double

    putStrLn ""
    putStrLn "Lists"
    putStrLn "-------------------------"
    putStr "head:           "
    qc prop_head
    putStr "tail:           "
    qc prop_tail
    putStr "cons:           "
    qc prop_cons
    putStr "snoc:           "
    qc prop_snoc
    putStr "take:           "
    qc prop_take
    putStr "drop:           "
    qc prop_drop
    putStr "map_id:         "
    qc prop_map_id
    putStr "filter_True:    "
    qc prop_filter_True
    putStr "the:            "
    qc prop_the
    putStr "last:           "
    qc prop_last
    putStr "init:           "
    qc prop_init
    putStr "null:           "
    qc prop_null
    putStr "length:         "
    qc prop_length
    putStr "index:          "
    qc prop_index
    putStr "reverse:        "
    qc prop_reverse
    putStr "append:         "
    qc prop_append
    putStr "groupWith_id:   "
    qc prop_groupWith_id
    putStr "sortWith_id:    "
    qc prop_sortWith_id

    putStrLn ""
    putStrLn "Special folds"
    putStrLn "-------------------------"
    putStr "and:            "
    qc prop_and
    putStr "or:             "
    qc prop_or
    putStr "any_zero:       "
    qc prop_any_zero
    putStr "all_zero:       "
    qc prop_all_zero
    putStr "sum_integer:    "
    qc prop_sum_integer
    putStr "sum_double:     "
    qc prop_sum_double
    putStr "concat:         "
    qc prop_concat
    putStr "concatMap:      "
    qc prop_concatMap
    putStr "maximum:        "
    qc prop_maximum
    putStr "minimum:        "
    qc prop_minimum

    putStrLn ""
    putStrLn "Sublists"
    putStrLn "-------------------------"
    putStr "splitAt:        "
    qc prop_splitAt
    putStr "takeWhile:      "
    qc prop_takeWhile
    putStr "dropWhile:      "
    qc prop_dropWhile
    putStr "span:           "
    qc prop_span
    putStr "break:          "
    qc prop_break

    putStrLn ""
    putStrLn "Zipping and unzipping lists"
    putStrLn "-------------------------"
    putStr "zip:            "
    qc prop_zip
    putStr "zipWith_plus:   "
    qc prop_zipWith_plus
    putStr "unzip:          "
    qc prop_unzip

    putStrLn ""
    putStrLn "Set operations"
    putStrLn "-------------------------"
    putStr "nub:            "
    qc prop_nub


runTest :: (Eq b, QA a, QA b, Show a, Show b)
        => (Q a -> Q b)
        -> (a -> b)
        -> a
        -> Property
runTest q f arg = monadicIO $ do
    c  <- run $ getConn
    db <- run $ fromQ c (q (Q.toQ arg))
    run $ HDBC.disconnect c
    let hs = f arg
    assert (db == hs)

testNotNull :: (Eq b, Q.QA a, Q.QA b, Show a, Show b)
            => (Q.Q [a] -> Q.Q b)
            -> ([a] -> b)
            -> [a]
            -> Property
testNotNull q f arg = not (null arg) ==> runTest q f arg

runTestDouble :: (QA a, Show a)
        => (Q a -> Q Double)
        -> (a -> Double)
        -> a
        -> Property
runTestDouble q f arg = monadicIO $ do
    c  <- run $ getConn
    db <- run $ fromQ c (q (Q.toQ arg))
    run $ HDBC.disconnect c
    let hs = f arg
    let eps = 1.0E-8 :: Double;    
    assert (abs(db - hs) < eps)



uncurry_Q :: (Q.QA a, Q.QA b) => (Q.Q a -> Q.Q b -> Q.Q c) -> Q.Q (a,b) -> Q.Q c
uncurry_Q q = uncurry q . Q.view

prop_unit :: () -> Property
prop_unit = runTest id id

prop_bool :: Bool -> Property
prop_bool = runTest id id

prop_integer :: Integer -> Property
prop_integer = runTest id id

prop_double :: Double -> Property
prop_double = runTestDouble id id

isValidXmlChar :: Char -> Bool
isValidXmlChar c =
     '\x0009' <= c && c <= '\x000A'
  || '\x000D' <= c && c <= '\x000D'
  || '\x0020' <= c && c <= '\xD7FF'
  || '\xE000' <= c && c <= '\xFFFD'
  || '\x10000'<= c && c <= '\x10FFFF'

prop_char :: Char -> Property
prop_char c = isPrint c ==> runTest id id c

prop_text :: Text -> Property
prop_text t = Text.all isPrint t ==> runTest id id t



--------------------------------------------------------------------------------
-- Equality & Ordering

prop_infix_and :: (Bool,Bool) -> Property
prop_infix_and = runTest (uncurry_Q (Q.&&)) (uncurry (&&))

prop_infix_or :: (Bool,Bool) -> Property
prop_infix_or = runTest (uncurry_Q (Q.||)) (uncurry (||))

prop_not :: Bool -> Property
prop_not = runTest Q.not not

prop_eq :: (Eq a, Q.QA a, Show a) => (a,a) -> Property
prop_eq = runTest (\q -> Q.fst q Q.== Q.snd q) (\(a,b) -> a == b)

prop_eq_int :: (Integer,Integer) -> Property
prop_eq_int = prop_eq

prop_neq :: (Eq a, Q.QA a, Show a) => (a,a) -> Property
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

prop_min_integer :: (Integer,Integer) -> Property
prop_min_integer = runTest (uncurry_Q Q.min) (uncurry min)

prop_max_integer :: (Integer,Integer) -> Property
prop_max_integer = runTest (uncurry_Q Q.max) (uncurry max)

prop_min_double :: (Double,Double) -> Property
prop_min_double = runTestDouble (uncurry_Q Q.min) (uncurry min)

prop_max_double :: (Double,Double) -> Property
prop_max_double = runTestDouble (uncurry_Q Q.max) (uncurry max)

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
prop_append = runTest (uncurry_Q (Q.><)) (\(a,b) -> a ++ b)

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

prop_sum_integer :: [Integer] -> Property
prop_sum_integer = runTest Q.sum sum

prop_sum_double :: [Double] -> Property
prop_sum_double = runTestDouble Q.sum sum

prop_concat :: [[Integer]] -> Property
prop_concat = runTest Q.concat concat

prop_concatMap :: [Integer] -> Property
prop_concatMap = runTest (Q.concatMap Q.singleton) (concatMap (\a -> [a]))


prop_maximum :: [Integer] -> Property
prop_maximum = testNotNull Q.maximum maximum

prop_minimum :: [Integer] -> Property
prop_minimum = testNotNull Q.minimum minimum

--------------------------------------------------------------------------------
-- Sublists

prop_splitAt :: (Integer, [Integer]) -> Property
prop_splitAt = runTest (uncurry_Q Q.splitAt) (\(a,b) -> splitAt (fromIntegral a) b)

prop_takeWhile :: (Integer, [Integer]) -> Property
prop_takeWhile = runTest (uncurry_Q $ Q.takeWhile . (Q.==))
                         (uncurry   $   takeWhile . (==))

prop_dropWhile :: (Integer, [Integer]) -> Property
prop_dropWhile = runTest (uncurry_Q $ Q.dropWhile . (Q.==))
                         (uncurry   $   dropWhile . (==))

prop_span :: (Integer, [Integer]) -> Property
prop_span = runTest (uncurry_Q $ Q.span . (Q.==))
                    (uncurry   $   span . (==) . fromIntegral)

prop_break :: (Integer, [Integer]) -> Property
prop_break = runTest (uncurry_Q $ Q.break . (Q.==))
                     (uncurry   $   break . (==) . fromIntegral)


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


--------------------------------------------------------------------------------
-- Conditionals

prop_cond :: Bool -> Property
prop_cond = runTest (Q.cond Q.empty (Q.toQ [0 :: Integer]))
                    (\b -> if b then [] else [0])

--------------------------------------------------------------------------------
-- Numerical Operations

prop_add_integer :: (Integer,Integer) -> Property
prop_add_integer = runTest (uncurry_Q (+)) (uncurry (+))

prop_add_double :: (Double,Double) -> Property
prop_add_double = runTestDouble (uncurry_Q (+)) (uncurry (+))

prop_mul_integer :: (Integer,Integer) -> Property
prop_mul_integer = runTest (uncurry_Q (*)) (uncurry (*))

prop_mul_double :: (Double,Double) -> Property
prop_mul_double = runTestDouble (uncurry_Q (*)) (uncurry (*))

prop_div_double :: (Double,Double) -> Property
prop_div_double (x,y) =
      y /= 0
  ==> runTestDouble (uncurry_Q (/)) (uncurry (/)) (x,y)

prop_integer_to_double :: Integer -> Property
prop_integer_to_double = runTestDouble Q.integerToDouble fromInteger

prop_abs_integer :: Integer -> Property
prop_abs_integer = runTest Q.abs abs

prop_abs_double :: Double -> Property
prop_abs_double = runTestDouble Q.abs abs

prop_signum_integer :: Integer -> Property
prop_signum_integer = runTest Q.signum signum

prop_signum_double :: Double -> Property
prop_signum_double = runTestDouble Q.signum signum

prop_negate_integer :: Integer -> Property
prop_negate_integer = runTest Q.negate negate

prop_negate_double :: Double -> Property
prop_negate_double = runTestDouble Q.negate negate