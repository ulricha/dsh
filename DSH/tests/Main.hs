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
import Data.Maybe
import Data.Either
import GHC.Exts

import Data.Text (Text)
import qualified Data.Text as Text

import Data.Char

instance Arbitrary Text where
  arbitrary = fmap Text.pack arbitrary

getConn :: IO Connection
getConn = connectPostgreSQL "user = 'giorgidz' password = '' host = 'localhost' dbname = 'giorgidz'"

qc:: Testable prop => prop -> IO ()
qc = quickCheckWith stdArgs{maxSuccess = 100, maxSize = 5}

putStrPad :: String -> IO ()
putStrPad s = putStr (s ++ replicate (32 - length s) ' ' )

main :: IO ()
main = do
    putStrLn "Supprted Types"
    putStrLn "--------------"
    putStrPad "()"
    qc prop_unit
    putStrPad "Bool"
    qc prop_bool
    putStrPad "Char"
    qc prop_char
    putStrPad "Text"
    qc prop_text
    putStrPad "Integer"
    qc prop_integer
    putStrPad "Double"
    qc prop_double
    putStrPad "[Integer]"
    qc prop_list_integer_1
    putStrPad "[[Integer]]"
    qc prop_list_integer_2
    putStrPad "[[[Integer]]]"
    qc prop_list_integer_3
    putStrPad "Maybe Integer"
    qc prop_maybe_integer
    putStrPad "Either Integer Integer: "
    qc prop_either_integer

    putStrLn ""
    putStrLn "Equality, Boolean Logic and Ordering"
    putStrLn "------------------------------------"
    putStrPad "&&"
    qc prop_infix_and
    putStrPad "||"
    qc prop_infix_or
    putStrPad "not"
    qc prop_not
    putStrPad "eq"
    qc prop_eq
    putStrPad "neq"
    qc prop_neq
    putStrPad "cond"
    qc prop_cond
    putStrPad "lt"
    qc prop_lt
    putStrPad "lte"
    qc prop_lte
    putStrPad "gt"
    qc prop_gt
    putStrPad "gte"
    qc prop_gte
    putStrPad "min_integer"
    qc prop_min_integer
    putStrPad "min_double"
    qc prop_min_double
    putStrPad "max_integer"
    qc prop_max_integer
    putStrPad "max_double"
    qc prop_max_double
    
    putStrLn ""
    putStrLn "Tuples"
    putStrLn "------"
    putStrPad "fst"
    qc prop_fst
    putStrPad "snd"
    qc prop_snd

    putStrLn ""
    putStrLn "Numerics:"
    putStrLn "-----------"
    putStrPad "add_integer"
    qc prop_add_integer
    putStrPad "add_double"
    qc prop_add_double
    putStrPad "mul_integer"
    qc prop_mul_integer
    putStrPad "mul_double"
    qc prop_mul_double
    putStrPad "div_double"
    qc prop_div_double
    putStrPad "integer_to_double: "
    qc prop_integer_to_double    
    putStrPad "abs_integer"
    qc prop_abs_integer
    putStrPad "abs_double"
    qc prop_abs_double
    putStrPad "signum_integer: "
    qc prop_signum_integer
    putStrPad "signum_double"
    qc prop_signum_double
    putStrPad "negate_integer: "
    qc prop_negate_integer
    putStrPad "negate_double"
    qc prop_negate_double

    putStrLn ""
    putStrLn "Maybe"
    putStrLn "-----"
    putStrPad "maybe"
    qc prop_maybe
    putStrPad "just"
    qc prop_just
    putStrPad "isJust"
    qc prop_isJust
    putStrPad "isNothing"
    qc prop_isNothing
    putStrPad "fromJust"
    qc prop_fromJust
    putStrPad "fromMaybe"
    qc prop_fromMaybe
    putStrPad "listToMaybe"
    qc prop_listToMaybe
    putStrPad "maybeToList"
    qc prop_maybeToList
    putStrPad "catMaybes"
    qc prop_catMaybes
    putStrPad "mapMaybe"
    qc prop_mapMaybe
    
    putStrLn ""
    putStrLn "Either"
    putStrLn "-----"
    putStrPad "left"
    qc prop_left
    putStrPad "right"
    qc prop_right
    putStrPad "isLeft"
    qc prop_isLeft
    putStrPad "isRight"
    qc prop_isRight
    putStrPad "either"
    qc prop_either
    putStrPad "lefts"
    qc prop_lefts
    putStrPad "rights"
    qc prop_rights
    putStrPad "partitionEithers"
    qc prop_partitionEithers

    putStrLn ""
    putStrLn "Lists"
    putStrLn "-----"
    putStrPad "head"
    qc prop_head
    putStrPad "tail"
    qc prop_tail
    putStrPad "cons"
    qc prop_cons
    putStrPad "snoc"
    qc prop_snoc
    putStrPad "take"
    qc prop_take
    putStrPad "drop"
    qc prop_drop
    putStrPad "map"
    qc prop_map
    putStrPad "filter"
    qc prop_filter
    putStrPad "the"
    qc prop_the
    putStrPad "last"
    qc prop_last
    putStrPad "init"
    qc prop_init
    putStrPad "null"
    qc prop_null
    putStrPad "length"
    qc prop_length
    putStrPad "index"
    qc prop_index
    putStrPad "reverse"
    qc prop_reverse
    putStrPad "append"
    qc prop_append
    putStrPad "groupWith"
    qc prop_groupWith
    putStrPad "sortWith"
    qc prop_sortWith
    putStrPad "and"
    qc prop_and
    putStrPad "or"
    qc prop_or
    putStrPad "any_zero"
    qc prop_any_zero
    putStrPad "all_zero"
    qc prop_all_zero
    putStrPad "sum_integer"
    qc prop_sum_integer
    putStrPad "sum_double"
    qc prop_sum_double
    putStrPad "concat"
    qc prop_concat
    putStrPad "concatMap"
    qc prop_concatMap
    putStrPad "maximum"
    qc prop_maximum
    putStrPad "minimum"
    qc prop_minimum
    putStrPad "splitAt"
    qc prop_splitAt
    putStrPad "takeWhile"
    qc prop_takeWhile
    putStrPad "dropWhile"
    qc prop_dropWhile
    putStrPad "span"
    qc prop_span
    putStrPad "break"
    qc prop_break
    putStrPad "elem"
    qc prop_elem
    putStrPad "notElem"
    qc prop_notElem
    putStrPad "lookup"
    qc prop_lookup
    putStrPad "zip"
    qc prop_zip
    putStrPad "zipWith"
    qc prop_zipWith
    putStrPad "unzip"
    qc prop_unzip
    putStrPad "nub"
    qc prop_nub

makeProp :: (Eq b, QA a, QA b, Show a, Show b)
            => (Q a -> Q b)
            -> (a -> b)
            -> a
            -> Property
makeProp f1 f2 arg = monadicIO $ do
    c  <- run getConn
    db <- run $ fromQ c $ f1 (Q.toQ arg)
    run (HDBC.disconnect c)
    let hs = f2 arg
    assert (db == hs)

makePropNotNull ::  (Eq b, QA a, QA b, Show a, Show b)
                    => (Q [a] -> Q b)
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
    c  <- run $ getConn
    db <- run $ fromQ c $ f1 (Q.toQ arg)
    run $ HDBC.disconnect c
    let hs = f2 arg
    let eps = 1.0E-8 :: Double;    
    assert (abs (db - hs) < eps)

uncurryQ :: (QA a, QA b) => (Q a -> Q b -> Q c) -> Q (a,b) -> Q c
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

prop_maybe_integer :: Maybe Integer -> Property
prop_maybe_integer = makeProp id id

prop_either_integer :: Either Integer Integer -> Property
prop_either_integer = makeProp id id

-- * Equality, Boolean Logic and Ordering

prop_infix_and :: (Bool,Bool) -> Property
prop_infix_and = makeProp (uncurryQ (Q.&&)) (uncurry (&&))

prop_infix_or :: (Bool,Bool) -> Property
prop_infix_or = makeProp (uncurryQ (Q.||)) (uncurry (||))

prop_not :: Bool -> Property
prop_not = makeProp Q.not not

prop_eq :: (Integer,Integer) -> Property
prop_eq = makeProp (uncurryQ (Q.==)) (uncurry (==))

prop_neq :: (Integer,Integer) -> Property
prop_neq = makeProp (uncurryQ (Q./=)) (uncurry (/=))

prop_cond :: Bool -> Property
prop_cond = makeProp (\b -> Q.cond b 0 1) (\b -> if b then (0 :: Integer) else 1)

prop_lt :: (Integer, Integer) -> Property
prop_lt = makeProp (uncurryQ (Q.<)) (uncurry (<))

prop_lte :: (Integer, Integer) -> Property
prop_lte = makeProp (uncurryQ (Q.<=)) (uncurry (<=))

prop_gt :: (Integer, Integer) -> Property
prop_gt = makeProp (uncurryQ (Q.>)) (uncurry (>))

prop_gte :: (Integer, Integer) -> Property
prop_gte = makeProp (uncurryQ (Q.>=)) (uncurry (>=))

prop_min_integer :: (Integer,Integer) -> Property
prop_min_integer = makeProp (uncurryQ Q.min) (uncurry min)

prop_max_integer :: (Integer,Integer) -> Property
prop_max_integer = makeProp (uncurryQ Q.max) (uncurry max)

prop_min_double :: (Double,Double) -> Property
prop_min_double = makePropDouble (uncurryQ Q.min) (uncurry min)

prop_max_double :: (Double,Double) -> Property
prop_max_double = makePropDouble (uncurryQ Q.max) (uncurry max)

-- * Maybe

prop_maybe :: (Integer, Maybe Integer) -> Property
prop_maybe =  makeProp (\a -> Q.maybe (Q.fst a) id (Q.snd a)) (\(i,mi) -> maybe i id mi)

prop_just :: Integer -> Property
prop_just = makeProp Q.just Just

prop_isJust :: Maybe Integer -> Property
prop_isJust = makeProp Q.isJust isJust

prop_isNothing :: Maybe Integer -> Property
prop_isNothing = makeProp Q.isNothing isNothing

prop_fromJust :: Maybe Integer -> Property
prop_fromJust mi = isJust mi ==> makeProp Q.fromJust fromJust mi

prop_fromMaybe :: (Integer,Maybe Integer) -> Property
prop_fromMaybe = makeProp (uncurryQ Q.fromMaybe) (uncurry fromMaybe)

prop_listToMaybe :: [Integer] -> Property
prop_listToMaybe = makeProp Q.listToMaybe listToMaybe

prop_maybeToList :: Maybe Integer -> Property
prop_maybeToList = makeProp Q.maybeToList maybeToList

prop_catMaybes :: [Maybe Integer] -> Property
prop_catMaybes = makeProp Q.catMaybes catMaybes

prop_mapMaybe :: [Maybe Integer] -> Property
prop_mapMaybe = makeProp (Q.mapMaybe id) (mapMaybe id)

-- * Either

prop_left :: Integer -> Property
prop_left = makeProp (Q.left :: Q Integer -> Q (Either Integer Integer)) Left

prop_right :: Integer -> Property
prop_right = makeProp (Q.right :: Q Integer -> Q (Either Integer Integer)) Right

prop_isLeft :: Either Integer Integer -> Property
prop_isLeft = makeProp Q.isLeft (\e -> case e of {Left _ -> True; Right _ -> False;})

prop_isRight :: Either Integer Integer -> Property
prop_isRight = makeProp Q.isRight (\e -> case e of {Left _ -> False; Right _ -> True;})

prop_either :: (Either Integer Integer) -> Property
prop_either =  makeProp (Q.either id id) (either id id)

prop_lefts :: [Either Integer Integer] -> Property
prop_lefts =  makeProp Q.lefts lefts

prop_rights :: [Either Integer Integer] -> Property
prop_rights =  makeProp Q.rights rights

prop_partitionEithers :: [Either Integer Integer] -> Property
prop_partitionEithers =  makeProp Q.partitionEithers partitionEithers

-- * Lists

prop_cons :: (Integer, [Integer]) -> Property
prop_cons = makeProp (uncurryQ (Q.<|)) (uncurry (:))

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

prop_the   :: [Integer] -> Property
prop_the l =
        allEqual l
    ==> makeProp Q.the the l
  where
    allEqual []     = False
    allEqual (x:xs) = all (x ==) xs

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

prop_map :: [Integer] -> Property
prop_map = makeProp (Q.map id) (map id)

prop_append :: ([Integer], [Integer]) -> Property
prop_append = makeProp (uncurryQ (Q.++)) (\(a,b) -> a ++ b)

prop_filter :: [Integer] -> Property
prop_filter = makeProp (Q.filter (const $ Q.toQ True)) (filter $ const True)

prop_groupWith :: [Integer] -> Property
prop_groupWith = makeProp (Q.groupWith id) (groupWith id)

prop_sortWith  :: [Integer] -> Property
prop_sortWith = makeProp (Q.sortWith id) (sortWith id)

prop_null :: [Integer] -> Property
prop_null = makeProp Q.null null

prop_length :: [Integer] -> Property
prop_length = makeProp Q.length ((fromIntegral :: Int -> Integer) . length)

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

prop_lookup :: (Integer, [(Integer,Integer)]) -> Property
prop_lookup = makeProp (uncurryQ $ Q.lookup)
                       (uncurry  $   lookup)

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

prop_snd :: (Integer, Integer) -> Property
prop_snd = makeProp Q.snd snd

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