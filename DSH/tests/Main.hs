{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE ViewPatterns #-}

module Main where

import qualified Database.DSH as Q
import Database.DSH (Q, QA)

-- import Database.DSH.Interpreter (fromQ)
#ifdef isDBPH 
import Database.DSH.Flattening (fromQ)
#elif isX100
import Database.DSH.Flattening (fromX100)
#define isDBPH 
#else
import Database.DSH.Compiler (fromQ)
#endif

#ifdef isX100
import Database.X100Client
#endif

#ifndef isX100
import qualified Database.HDBC as HDBC
import Database.HDBC.PostgreSQL
#endif


import System.Environment
import Test.Framework (Test, defaultMainWithArgs, testGroup)
import Test.Framework.Providers.QuickCheck2 (testProperty)
import Test.QuickCheck
import Test.QuickCheck.Monadic

import Data.List
import GHC.Exts

import Data.Text (Text)
import qualified Data.Text as Text

import Data.Char

instance Arbitrary Text where
  arbitrary = fmap Text.pack arbitrary

#ifdef isX100
getConn :: IO X100Info
getConn = return $ x100Info "localhost" 48130 Nothing    
#else
getConn :: IO Connection
getConn = connectPostgreSQL "user = 'postgres' password = 'haskell98' host = 'localhost' port = '5432' dbname = 'ferry'"
#endif

main :: IO ()
main = do
            args <- getArgs
            let args' = if or $ map (isPrefixOf "-s") args
                         then args
                         else "-s5":args
            defaultMainWithArgs tests args'

tests :: [Test]
tests = 
    [
      testGroup "Supported Types"
        [ testProperty "()" $ prop_unit
        , testProperty "()" $ prop_unit
        , testProperty "Bool" $ prop_bool
        , testProperty "Char" $ prop_char
        , testProperty "Text" $ prop_text
        , testProperty "Integer" $ prop_integer
        , testProperty "Double" $ prop_double
        , testProperty "[Integer]" $ prop_list_integer_1
        , testProperty "[[Integer]]" $ prop_list_integer_2
        , testProperty "[[[Integer]]]" $ prop_list_integer_3
#ifndef isDBPH
        {-
        , testProperty "Maybe Integer" $ prop_maybe_integer
        , testProperty "Either Integer Integer" $ prop_either_integer
        -}
#endif
        ]
    , testGroup "Equality, Boolean Logic and Ordering"
        [ testProperty "&&" $ prop_infix_and
        , testProperty "||" $ prop_infix_or
        , testProperty "not" $ prop_not
        , testProperty "eq" $ prop_eq
        , testProperty "neq" $ prop_neq
        , testProperty "cond" $ prop_cond
        , testProperty "lt" $ prop_lt
        , testProperty "lte" $ prop_lte
        , testProperty "gt" $ prop_gt
        , testProperty "gte" $ prop_gte
#ifndef isDBPH
        , testProperty "min_integer" $ prop_min_integer
        , testProperty "min_double" $ prop_min_double
        , testProperty "max_integer" $ prop_max_integer
        , testProperty "max_double" $ prop_max_double
#endif
        ]
    , testGroup "Tuples"
        [ testProperty "fst" $ prop_fst
        , testProperty "snd" $ prop_snd
        ]
    , testGroup "Numerics"
        [ testProperty "add_integer" $ prop_add_integer
        , testProperty "add_double" $ prop_add_double
        , testProperty "mul_integer" $ prop_mul_integer
        , testProperty "mul_double" $ prop_mul_double
        , testProperty "div_double" $ prop_div_double
#ifndef isDBPH
        , testProperty "integer_to_double" $ prop_integer_to_double    
        , testProperty "abs_integer" $ prop_abs_integer
        , testProperty "abs_double" $ prop_abs_double
        , testProperty "signum_integer" $ prop_signum_integer
        , testProperty "signum_double" $ prop_signum_double
        , testProperty "negate_integer" $ prop_negate_integer
        , testProperty "negate_double" $ prop_negate_double
#endif
        ]
    , testGroup "Lists"
        [
#ifndef isDBPH 
          testProperty "head" $ prop_head
        , testProperty "tail" $ prop_tail
        , 
#endif        
         testProperty "cons" $ prop_cons
#ifndef isDBPH
        , testProperty "snoc" $ prop_snoc
        , testProperty "take" $ prop_take
        , testProperty "drop" $ prop_drop
        , testProperty "take ++ drop" $ prop_takedrop
#endif

        , testProperty "map" $ prop_map

#ifndef isDBPH
        , testProperty "filter" $ prop_filter
#endif
        , testProperty "the" $ prop_the
#ifndef isDBPH
        , testProperty "last" $ prop_last
        , testProperty "init" $ prop_init
        , testProperty "null" $ prop_null
#endif
        , testProperty "length" $ prop_length
        , testProperty "length tuple list" $ prop_length_tuple
#ifndef isDBPH
        , testProperty "index" $ prop_index
        , testProperty "reverse" $ prop_reverse
        , testProperty "append" $ prop_append
#endif
        , testProperty "groupWith" $ prop_groupWith
        , testProperty "groupWith length" $ prop_groupWith_length
        , testProperty "sortWith" $ prop_sortWith
#ifndef isDBPH
        , testProperty "and" $ prop_and
        , testProperty "or" $ prop_or
        , testProperty "any_zero" $ prop_any_zero
        , testProperty "all_zero" $ prop_all_zero
#endif
        , testProperty "sum_integer" $ prop_sum_integer
        , testProperty "sum_double" $ prop_sum_double
        , testProperty "concat" $ prop_concat
        , testProperty "concatMap" $ prop_concatMap
#ifndef isDBPH
        , testProperty "maximum" $ prop_maximum
        , testProperty "minimum" $ prop_minimum
        , testProperty "splitAt" $ prop_splitAt
        , testProperty "takeWhile" $ prop_takeWhile
        , testProperty "dropWhile" $ prop_dropWhile
        , testProperty "span" $ prop_span
        , testProperty "break" $ prop_break
        , testProperty "elem" $ prop_elem
        , testProperty "notElem" $ prop_notElem
        , testProperty "zip" $ prop_zip
        , testProperty "zipWith" $ prop_zipWith
        , testProperty "unzip" $ prop_unzip
        , testProperty "nub" $ prop_nub
#endif
        ]
    , testGroup "Lifted operations"
        [ testProperty "Lifted &&" $ prop_infix_map_and
        , testProperty "Lifted ||" $ prop_infix_map_or
        , testProperty "Lifted not" $ prop_map_not
        , testProperty "Lifted eq" $ prop_map_eq
        , testProperty "Lifted neq" $ prop_map_neq
        , testProperty "Lifted cond" $ prop_map_cond
        , testProperty "Lifted cond tuples" $ prop_map_cond_tuples
        , testProperty "Lifted cond + concat" $ prop_concatmapcond
        , testProperty "Lifted lt" $ prop_map_lt
        , testProperty "Lifted lte" $ prop_map_lte
        , testProperty "Lifted gt" $ prop_map_gt
        , testProperty "Lifted gte" $ prop_map_gte
        , testProperty "Lifted cons" $ prop_map_cons
        , testProperty "Lifted concat" $ prop_map_concat
        , testProperty "Lifted fst" $ prop_map_fst
        , testProperty "Lifted snd" $ prop_map_snd
        , testProperty "Lifted the" $ prop_map_the
        --, testProperty "Lifed and" $ prop_map_and
        , testProperty "map (map (*2))" $ prop_map_map_mul
        , testProperty "map (map (map (*2)))" $ prop_map_map_map_mul
        , testProperty "map (\\x -> map (\\y -> x + y) ..) .." $ prop_map_map_add
        , testProperty "Lifted groupWith" $ prop_map_groupWith
        , testProperty "Lifted sortWith" $ prop_map_sortWith
        , testProperty "Lifted sortWith length" $ prop_map_sortWith_length
        , testProperty "Lifted groupWith length" $ prop_map_groupWith_length
        , testProperty "Lifted length" $ prop_map_length
        , testProperty "Lifted length on [[(a,b)]]" $ prop_map_length_tuple
        {- This test fails at least on X100: The X100 result is correct, but the order of elements
           with the same ordering criterium is different from the one generated by GHC.Exts.sortWith,
           which is not a stable sort. GHC.Exts.sortWith documentation does not specify wether it
           sorts in a stable way or not. -}
        , testProperty "Sortwith length nested" $ prop_sortWith_length_nest
        , testProperty "GroupWith length nested" $ prop_groupWith_length_nest
        ]
    ]

makeProp :: (Eq b, QA a, QA b, Show a, Show b)
            => (Q a -> Q b)
            -> (a -> b)
            -> a
            -> Property
makeProp f1 f2 arg = monadicIO $ do
#ifdef isX100
    c  <- run $ getConn
    db <- run $ fromX100 c $ f1 (Q.toQ arg)
#else
    c  <- run $ getConn
    db <- run $ fromQ c $ f1 (Q.toQ arg)
    run $ HDBC.disconnect c
#endif
    let hs = f2 arg
    assert (db == hs)

makePropNotNull ::  (Eq b, Q.QA a, Q.QA b, Show a, Show b)
                    => (Q.Q [a] -> Q.Q b)
                    -> ([a] -> b)
                    -> [a]
                    -> Property
makePropNotNull q f arg = not (null arg) ==> makeProp q f arg

makePropDouble :: (QA a, Show a)
                  => (Q a -> Q Double)
                  -> (a -> Double)
                  -> a
                  -> Property
makePropDouble f1 f2 arg = monadicIO $ do
#ifdef isX100
    c  <- run $ getConn
    db <- run $ fromX100 c $ f1 (Q.toQ arg)
#else
    c  <- run $ getConn
    db <- run $ fromQ c $ f1 (Q.toQ arg)
    run $ HDBC.disconnect c
#endif
    let hs = f2 arg
    let eps = 1.0E-8 :: Double;    
    assert (abs (db - hs) < eps)

uncurryQ :: (Q.QA a, Q.QA b) => (Q.Q a -> Q.Q b -> Q.Q c) -> Q.Q (a,b) -> Q.Q c
uncurryQ f = uncurry f . Q.view

-- * Supported Types

prop_unit :: () -> Property
prop_unit = makeProp id id

prop_bool :: Bool -> Property
prop_bool = makeProp id id

prop_integer :: Integer -> Property
prop_integer = makeProp id id

prop_double :: Double -> Property
prop_double = makePropDouble id id

prop_char :: Char -> Property
prop_char c = isPrint c ==> makeProp id id c

prop_text :: Text -> Property
prop_text t = Text.all isPrint t ==> makeProp id id t

prop_list_integer_1 :: [Integer] -> Property
prop_list_integer_1 = makeProp id id

prop_list_integer_2 :: [[Integer]] -> Property
prop_list_integer_2 = makeProp id id

prop_list_integer_3 :: [[[Integer]]] -> Property
prop_list_integer_3 = makeProp id id

-- * Equality, Boolean Logic and Ordering

prop_infix_and :: (Bool,Bool) -> Property
prop_infix_and = makeProp (uncurryQ (Q.&&)) (uncurry (&&))

prop_infix_map_and :: (Bool, [Bool]) -> Property
prop_infix_map_and = makeProp (\x -> Q.map ((Q.fst x) Q.&&) $ Q.snd x) (\(x,xs) -> map (x &&) xs)
                     
prop_map_and :: [[Bool]] -> Property
prop_map_and = makeProp (Q.map Q.and) (map and)

prop_infix_or :: (Bool,Bool) -> Property
prop_infix_or = makeProp (uncurryQ (Q.||)) (uncurry (||))

prop_infix_map_or :: (Bool, [Bool]) -> Property
prop_infix_map_or = makeProp (\x -> Q.map ((Q.fst x) Q.||) $ Q.snd x) (\(x,xs) -> map (x ||) xs)

prop_not :: Bool -> Property
prop_not = makeProp Q.not not

prop_map_not :: [Bool] -> Property
prop_map_not = makeProp (Q.map Q.not) (map not)

prop_eq :: (Integer,Integer) -> Property
prop_eq = makeProp (uncurryQ (Q.==)) (uncurry (==))

prop_map_eq :: (Integer, [Integer]) -> Property
prop_map_eq = makeProp (\x -> Q.map ((Q.fst x) Q.==) $ Q.snd x) (\(x,xs) -> map (x ==) xs)

prop_neq :: (Integer,Integer) -> Property
prop_neq = makeProp (uncurryQ (Q./=)) (uncurry (/=))

prop_map_neq :: (Integer, [Integer]) -> Property
prop_map_neq = makeProp (\x -> Q.map ((Q.fst x) Q./=) $ Q.snd x) (\(x,xs) -> map (x /=) xs)

prop_cond :: Bool -> Property
prop_cond = makeProp (\b -> Q.cond b (0 :: Q Integer) 1) (\b -> if b then 0 else 1)

prop_map_cond :: [Bool] -> Property
prop_map_cond = makeProp (Q.map (\b -> Q.cond b (0 :: Q Integer) 1)) (map (\b -> if b then 0 else 1))

prop_map_cond_tuples :: [Bool] -> Property
prop_map_cond_tuples = makeProp (Q.map (\b -> Q.cond b (Q.toQ (0, 10) :: Q (Integer, Integer)) (Q.toQ (1, 11)))) (map (\b -> if b then (0, 10) else (1, 11)))

prop_concatmapcond :: [Integer] -> Property
prop_concatmapcond l1 = 
        -- FIXME remove precondition as soon as X100 is fixed
	(not $ null l1)
	==>
	makeProp q n l1
        where q l = Q.concatMap (\x -> Q.cond ((Q.>) x (Q.toQ 0)) (x Q.<| el) el) l
              n l = concatMap (\x -> if x > 0 then [x] else []) l
              el = Q.toQ []

prop_lt :: (Integer, Integer) -> Property
prop_lt = makeProp (uncurryQ (Q.<)) (uncurry (<))

prop_map_lt :: (Integer, [Integer]) -> Property
prop_map_lt = makeProp (\x -> Q.map ((Q.fst x) Q.<) $ Q.snd x) (\(x,xs) -> map (x <) xs)

prop_lte :: (Integer, Integer) -> Property
prop_lte = makeProp (uncurryQ (Q.<=)) (uncurry (<=))

prop_map_lte :: (Integer, [Integer]) -> Property
prop_map_lte = makeProp (\x -> Q.map ((Q.fst x) Q.<=) $ Q.snd x) (\(x,xs) -> map (x <=) xs)

prop_gt :: (Integer, Integer) -> Property
prop_gt = makeProp (uncurryQ (Q.>)) (uncurry (>))

prop_map_gt :: (Integer, [Integer]) -> Property
prop_map_gt = makeProp (\x -> Q.map ((Q.fst x) Q.>) $ Q.snd x) (\(x,xs) -> map (x >) xs)

prop_gte :: (Integer, Integer) -> Property
prop_gte = makeProp (uncurryQ (Q.>=)) (uncurry (>=))

prop_map_gte :: (Integer, [Integer]) -> Property
prop_map_gte = makeProp (\x -> Q.map ((Q.fst x) Q.>=) $ Q.snd x) (\(x,xs) -> map (x >=) xs)

prop_min_integer :: (Integer,Integer) -> Property
prop_min_integer = makeProp (uncurryQ Q.min) (uncurry min)

prop_max_integer :: (Integer,Integer) -> Property
prop_max_integer = makeProp (uncurryQ Q.max) (uncurry max)

prop_min_double :: (Double,Double) -> Property
prop_min_double = makePropDouble (uncurryQ Q.min) (uncurry min)

prop_max_double :: (Double,Double) -> Property
prop_max_double = makePropDouble (uncurryQ Q.max) (uncurry max)

-- * Lists

prop_cons :: (Integer, [Integer]) -> Property
prop_cons = makeProp (uncurryQ (Q.<|)) (uncurry (:))

prop_map_cons :: (Integer, [[Integer]]) -> Property
prop_map_cons = makeProp (\x -> Q.map ((Q.fst x) Q.<|) $ Q.snd x) (\(x,xs) -> map (x:) xs)

prop_snoc :: ([Integer], Integer) -> Property
prop_snoc = makeProp (uncurryQ (Q.|>)) (\(a,b) -> a ++ [b])

prop_singleton :: Integer -> Property
prop_singleton = makeProp Q.singleton (\x -> [x])

prop_head  :: [Integer] -> Property
prop_head  = makePropNotNull Q.head head

prop_tail  :: [Integer] -> Property
prop_tail  = makePropNotNull Q.tail tail

prop_last  :: [Integer] -> Property
prop_last  = makePropNotNull Q.last last

prop_init  :: [Integer] -> Property
prop_init  = makePropNotNull Q.init init

prop_the   :: (Int, Integer) -> Property
prop_the (n, i) = 
  n > 0
  ==>
  let l = replicate n i in makeProp Q.the the l
                           
prop_map_the :: [(Int, Integer)] -> Property
prop_map_the ps =
  let ps' = filter ((>0) . fst) ps in
  (length ps') > 0
  ==>
  let xss = map (\(n, i) -> replicate n i) ps' in
  makeProp (Q.map Q.the) (map the) xss

prop_index :: ([Integer], Integer)  -> Property
prop_index (l, i) =
        i > 0 && i < fromIntegral (length l)
    ==> makeProp (uncurryQ (Q.!!))
                 (\(a,b) -> a !! fromIntegral b)
                 (l, i)

prop_take :: (Integer, [Integer]) -> Property
prop_take = makeProp (uncurryQ Q.take) (\(n,l) -> take (fromIntegral n) l)

prop_drop :: (Integer, [Integer]) -> Property
prop_drop = makeProp (uncurryQ Q.drop) (\(n,l) -> drop (fromIntegral n) l)

prop_takedrop :: (Integer, [Integer]) -> Property
prop_takedrop = makeProp takedrop_q takedrop
  where takedrop_q p = Q.append ((uncurryQ Q.take) p) ((uncurryQ Q.drop) p)
        takedrop (n, l) = (take (fromIntegral n) l) ++ (drop (fromIntegral n) l)

prop_map :: [Integer] -> Property
prop_map = makeProp (Q.map id) (map id)

prop_map_map_mul :: [[Integer]] -> Property
prop_map_map_mul = makeProp (Q.map (Q.map (*2))) (map (map (*2)))

prop_map_map_add :: ([Integer], [Integer]) -> Property
prop_map_map_add = makeProp (\z -> Q.map (\x -> (Q.map (\y -> x + y) $ Q.snd z)) $ Q.fst z) (\(l,r) -> map (\x -> map (\y -> x + y) r) l)
                   
prop_map_map_map_mul :: [[[Integer]]] -> Property
prop_map_map_map_mul = makeProp (Q.map (Q.map (Q.map (*2)))) (map (map (map (*2))))

prop_append :: ([Integer], [Integer]) -> Property
prop_append = makeProp (uncurryQ (Q.><)) (\(a,b) -> a ++ b)

prop_filter :: [Integer] -> Property
prop_filter = makeProp (Q.filter (const $ Q.toQ True)) (filter $ const True)

prop_groupWith :: [Integer] -> Property
prop_groupWith = makeProp (Q.groupWith id) (groupWith id)

prop_map_groupWith :: [[Integer]] -> Property
prop_map_groupWith = makeProp (Q.map (Q.groupWith id)) (map (groupWith id))
                     
prop_groupWith_length :: [[Integer]] -> Property
prop_groupWith_length = makeProp (Q.groupWith Q.length) (groupWith length)

prop_sortWith  :: [Integer] -> Property
prop_sortWith = makeProp (Q.sortWith id) (sortWith id)

prop_map_sortWith :: [[Integer]] -> Property
prop_map_sortWith = makeProp (Q.map (Q.sortWith id)) (map (sortWith id))

prop_map_sortWith_length :: [[[Integer]]] -> Property
prop_map_sortWith_length = makeProp (Q.map (Q.sortWith Q.length)) (map (sortWith length))
                           
prop_map_groupWith_length :: [[[Integer]]] -> Property
prop_map_groupWith_length = makeProp (Q.map (Q.groupWith Q.length)) (map (groupWith length))

prop_sortWith_length_nest  :: [[[Integer]]] -> Property
prop_sortWith_length_nest = makeProp (Q.sortWith Q.length) (sortWith length)
                            
prop_groupWith_length_nest :: [[[Integer]]] -> Property
prop_groupWith_length_nest = makeProp (Q.groupWith Q.length) (groupWith length)

prop_null :: [Integer] -> Property
prop_null = makeProp Q.null null

prop_length :: [Integer] -> Property
prop_length = makeProp Q.length (fromIntegral . length)

prop_length_tuple :: [(Integer, Integer)] -> Property
prop_length_tuple = makeProp Q.length (fromIntegral . length)

prop_map_length :: [[Integer]] -> Property
prop_map_length = makeProp (Q.map Q.length) (map (fromIntegral . length))

prop_map_length_tuple :: [[(Integer, Integer)]] -> Property
prop_map_length_tuple = makeProp (Q.map Q.length) (map (fromIntegral . length))

prop_reverse :: [Integer] -> Property
prop_reverse = makeProp Q.reverse reverse

prop_and :: [Bool] -> Property
prop_and = makeProp Q.and and
           

prop_or :: [Bool] -> Property
prop_or = makeProp Q.or or

prop_any_zero :: [Integer] -> Property
prop_any_zero = makeProp (Q.any (Q.== 0)) (any (== 0))

prop_all_zero :: [Integer] -> Property
prop_all_zero = makeProp (Q.all (Q.== 0)) (all (== 0))

prop_sum_integer :: [Integer] -> Property
prop_sum_integer = makeProp Q.sum sum

prop_sum_double :: [Double] -> Property
prop_sum_double = makePropDouble Q.sum sum

prop_concat :: [[Integer]] -> Property
prop_concat = makeProp Q.concat concat
              
prop_map_concat :: [[[Integer]]] -> Property
prop_map_concat = makeProp (Q.map Q.concat) (map concat)

prop_concatMap :: [Integer] -> Property
prop_concatMap = makeProp (Q.concatMap Q.singleton) (concatMap (\a -> [a]))

prop_maximum :: [Integer] -> Property
prop_maximum = makePropNotNull Q.maximum maximum

prop_minimum :: [Integer] -> Property
prop_minimum = makePropNotNull Q.minimum minimum

prop_splitAt :: (Integer, [Integer]) -> Property
prop_splitAt = makeProp (uncurryQ Q.splitAt) (\(a,b) -> splitAt (fromIntegral a) b)

prop_takeWhile :: (Integer, [Integer]) -> Property
prop_takeWhile = makeProp (uncurryQ $ Q.takeWhile . (Q.==))
                         (uncurry   $   takeWhile . (==))

prop_dropWhile :: (Integer, [Integer]) -> Property
prop_dropWhile = makeProp (uncurryQ $ Q.dropWhile . (Q.==))
                         (uncurry   $   dropWhile . (==))

prop_span :: (Integer, [Integer]) -> Property
prop_span = makeProp (uncurryQ $ Q.span . (Q.==))
                     (uncurry   $   span . (==) . fromIntegral)

prop_break :: (Integer, [Integer]) -> Property
prop_break = makeProp (uncurryQ $ Q.break . (Q.==))
                     (uncurry   $   break . (==) . fromIntegral)

prop_elem :: (Integer, [Integer]) -> Property
prop_elem = makeProp (uncurryQ $ Q.elem)
                     (uncurry  $   elem)

prop_notElem :: (Integer, [Integer]) -> Property
prop_notElem = makeProp (uncurryQ $ Q.notElem)
                        (uncurry  $   notElem)

prop_zip :: ([Integer], [Integer]) -> Property
prop_zip = makeProp (uncurryQ Q.zip) (uncurry zip)

prop_zipWith :: ([Integer], [Integer]) -> Property
prop_zipWith = makeProp (uncurryQ $ Q.zipWith (+)) (uncurry $ zipWith (+))

prop_unzip :: [(Integer, Integer)] -> Property
prop_unzip = makeProp Q.unzip unzip

prop_nub :: [Integer] -> Property
prop_nub = makeProp Q.nub nub

-- * Tuples

prop_fst :: (Integer, Integer) -> Property
prop_fst = makeProp Q.fst fst
           
prop_map_fst :: [(Integer, Integer)] -> Property
prop_map_fst = makeProp (Q.map Q.fst) (map fst)

prop_snd :: (Integer, Integer) -> Property
prop_snd = makeProp Q.snd snd
           
prop_map_snd :: [(Integer, Integer)] -> Property
prop_map_snd = makeProp (Q.map Q.snd) (map snd)

-- * Numerics

prop_add_integer :: (Integer,Integer) -> Property
prop_add_integer = makeProp (uncurryQ (+)) (uncurry (+))

prop_add_double :: (Double,Double) -> Property
prop_add_double = makePropDouble (uncurryQ (+)) (uncurry (+))

prop_mul_integer :: (Integer,Integer) -> Property
prop_mul_integer = makeProp (uncurryQ (*)) (uncurry (*))

prop_mul_double :: (Double,Double) -> Property
prop_mul_double = makePropDouble (uncurryQ (*)) (uncurry (*))

prop_div_double :: (Double,Double) -> Property
prop_div_double (x,y) =
      y /= 0
  ==> makePropDouble (uncurryQ (/)) (uncurry (/)) (x,y)

prop_integer_to_double :: Integer -> Property
prop_integer_to_double = makePropDouble Q.integerToDouble fromInteger

prop_abs_integer :: Integer -> Property
prop_abs_integer = makeProp Q.abs abs

prop_abs_double :: Double -> Property
prop_abs_double = makePropDouble Q.abs abs

prop_signum_integer :: Integer -> Property
prop_signum_integer = makeProp Q.signum signum

prop_signum_double :: Double -> Property
prop_signum_double = makePropDouble Q.signum signum

prop_negate_integer :: Integer -> Property
prop_negate_integer = makeProp Q.negate negate

prop_negate_double :: Double -> Property
prop_negate_double = makePropDouble Q.negate negate
