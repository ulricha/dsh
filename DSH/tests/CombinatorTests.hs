{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module CombinatorTests 
    ( tests_types
    , tests_boolean
    , tests_tuples
    , tests_numerics
    , tests_maybe
    , tests_either
    , tests_lists
    , tests_lifted
    , tests_combinators_hunit
    ) where

import           Common

import qualified Database.DSH as Q

import           Test.QuickCheck
import           Test.HUnit(Assertion)
import           Test.Framework (Test, testGroup)
import           Test.Framework.Providers.QuickCheck2 (testProperty)
import           Test.Framework.Providers.HUnit
import           Data.DeriveTH

import           Data.Char
import           Data.Text (Text)
import qualified Data.Text as Text

import           Data.List
import           Data.Maybe
import           Data.Either
import           GHC.Exts

data D0 = C01 deriving (Eq,Ord,Show)

derive makeArbitrary ''D0
Q.deriveDSH ''D0

data D1 a = C11 a deriving (Eq,Ord,Show)

derive makeArbitrary ''D1
Q.deriveDSH ''D1

data D2 a b = C21 a b b a deriving (Eq,Ord,Show)

derive makeArbitrary ''D2
Q.deriveDSH ''D2

data D3 = C31 
        | C32 
        deriving (Eq,Ord,Show)

derive makeArbitrary ''D3
Q.deriveDSH ''D3

data D4 a = C41 a 
          | C42 
          deriving (Eq,Ord,Show)

derive makeArbitrary ''D4
Q.deriveDSH ''D4

data D5 a = C51 a 
          | C52 
          | C53 a a 
          | C54 a a a 
          deriving (Eq,Ord,Show)

derive makeArbitrary ''D5
Q.deriveDSH ''D5

data D6 a b c d e = C61 { c611 :: a, c612 :: (a,b,c,d) } 
                  | C62 
                  | C63 a b 
                  | C64 (a,b,c) 
                  | C65 a b c d e 
                  deriving (Eq,Ord,Show)

derive makeArbitrary ''D6
Q.deriveDSH ''D6

tests_types :: Test
tests_types = testGroup "Supported Types"
  [ testProperty "()" $ prop_unit
  , testProperty "Bool" $ prop_bool
  , testProperty "Char" $ prop_char
  , testProperty "Text" $ prop_text
  , testProperty "Integer" $ prop_integer
  , testProperty "Double" $ prop_double
  , testProperty "[Integer]" $ prop_list_integer_1
  , testProperty "[[Integer]]" $ prop_list_integer_2
  , testProperty "[[[Integer]]]" $ prop_list_integer_3
  , testProperty "[(Integer, Integer)]" $ prop_list_tuple_integer
  , testProperty "([], [])" $ prop_tuple_list_integer
  , testProperty "Maybe Integer" $ prop_maybe_integer
  , testProperty "Either Integer Integer" $ prop_either_integer
  , testProperty "D0" $ prop_d0
  , testProperty "D1" $ prop_d1
  , testProperty "D2" $ prop_d2
  , testProperty "D3" $ prop_d3
  , testProperty "D4" $ prop_d4
  , testProperty "D5" $ prop_d5
  , testProperty "D6" $ prop_d6
  ]

tests_boolean :: Test
tests_boolean = testGroup "Equality, Boolean Logic and Ordering"
  [ testProperty "&&" $ prop_infix_and
  , testProperty "||" $ prop_infix_or
  , testProperty "not" $ prop_not
  , testProperty "eq" $ prop_eq
  , testProperty "neq" $ prop_neq
  , testProperty "cond" $ prop_cond
  , testProperty "cond tuples" $ prop_cond_tuples
  , testProperty "cond ([[Integer]], [[Integer]])" $ prop_cond_list_tuples
  , testProperty "lt" $ prop_lt
  , testProperty "lte" $ prop_lte
  , testProperty "gt" $ prop_gt
  , testProperty "gte" $ prop_gte
  , testProperty "min_integer" $ prop_min_integer
  , testProperty "min_double" $ prop_min_double
  , testProperty "max_integer" $ prop_max_integer
  , testProperty "max_double" $ prop_max_double
  ]

tests_tuples :: Test
tests_tuples = testGroup "Tuples"
  [ testProperty "fst" $ prop_fst
  , testProperty "snd" $ prop_snd
  , testProperty "fst ([], [])" prop_fst_nested
  , testProperty "snd ([], [])" prop_snd_nested
  ]

tests_numerics :: Test
tests_numerics = testGroup "Numerics"
  [ testProperty "add_integer" $ prop_add_integer
  , testProperty "add_double" $ prop_add_double
  , testProperty "mul_integer" $ prop_mul_integer
  , testProperty "mul_double" $ prop_mul_double
  , testProperty "div_double" $ prop_div_double
  , testProperty "integer_to_double" $ prop_integer_to_double
  , testProperty "integer_to_double_+" $ prop_integer_to_double_arith
  , testProperty "abs_integer" $ prop_abs_integer
  , testProperty "abs_double" $ prop_abs_double
  , testProperty "signum_integer" $ prop_signum_integer
  , testProperty "signum_double" $ prop_signum_double
  , testProperty "negate_integer" $ prop_negate_integer
  , testProperty "negate_double" $ prop_negate_double
  , testProperty "trig_sin" $ prop_trig_sin
  , testProperty "trig_cos" $ prop_trig_cos
  , testProperty "trig_tan" $ prop_trig_tan
  , testProperty "trig_asin" $ prop_trig_asin
  , testProperty "trig_acos" $ prop_trig_acos
  , testProperty "trig_atan" $ prop_trig_atan
  , testProperty "sqrt" $ prop_sqrt
  , testProperty "log" $ prop_log
  , testProperty "exp" $ prop_exp
  ]

tests_maybe :: Test
tests_maybe = testGroup "Maybe"
        [ testProperty "maybe" $ prop_maybe
        , testProperty "just" $ prop_just
        , testProperty "isJust" $ prop_isJust
        , testProperty "isNothing" $ prop_isNothing
        , testProperty "fromJust" $ prop_fromJust
        , testProperty "fromMaybe" $ prop_fromMaybe
        , testProperty "listToMaybe" $ prop_listToMaybe
        , testProperty "maybeToList" $ prop_maybeToList
        , testProperty "catMaybes" $ prop_catMaybes
        , testProperty "mapMaybe" $ prop_mapMaybe
        ]

tests_either :: Test
tests_either = testGroup "Either"
        [ testProperty "left" $ prop_left
        , testProperty "right" $ prop_right
        , testProperty "isLeft" $ prop_isLeft
        , testProperty "isRight" $ prop_isRight
        , testProperty "either" $ prop_either
        , testProperty "lefts" $ prop_lefts
        , testProperty "rights" $ prop_rights
        , testProperty "partitionEithers" $ prop_partitionEithers
        ]

tests_lists :: Test
tests_lists = testGroup "Lists"
        [ testProperty "singleton" prop_singleton
        , testProperty "head" $ prop_head
        , testProperty "tail" $ prop_tail
        , testProperty "cons" $ prop_cons
        , testProperty "snoc" $ prop_snoc
        , testProperty "take" $ prop_take
        , testProperty "drop" $ prop_drop
        , testProperty "take ++ drop" $ prop_takedrop
        , testProperty "map" $ prop_map
        , testProperty "filter" $ prop_filter
        , testProperty "the" $ prop_the
        , testProperty "last" $ prop_last
        , testProperty "init" $ prop_init
        , testProperty "null" $ prop_null
        , testProperty "length" $ prop_length
        , testProperty "length tuple list" $ prop_length_tuple
        , testProperty "index [Integer]" $ prop_index
        , testProperty "index [(Integer, [Integer])]" $ prop_index_pair
        , testProperty "index [[]]" $ prop_index_nest
        , testProperty "reverse" $ prop_reverse
        , testProperty "reverse [[]]" $ prop_reverse_nest
        , testProperty "append" $ prop_append
        , testProperty "append nest" $ prop_append_nest
        , testProperty "groupWith" $ prop_groupWith
        , testProperty "groupWithKey" $ prop_groupWithKey
        , testProperty "groupWith length" $ prop_groupWith_length
        , testProperty "groupWithKey length" $ prop_groupWithKey_length
        , testProperty "sortWith" $ prop_sortWith
        , testProperty "and" $ prop_and
        , testProperty "or" $ prop_or
        , testProperty "any_zero" $ prop_any_zero
        , testProperty "all_zero" $ prop_all_zero
        , testProperty "sum_integer" $ prop_sum_integer
        , testProperty "sum_double" $ prop_sum_double
        , testProperty "avg_integer" $ prop_avg_integer
        , testProperty "avg_double" $ prop_avg_double
        , testProperty "concat" $ prop_concat
        , testProperty "concatMap" $ prop_concatMap
        , testProperty "maximum" $ prop_maximum
        , testProperty "minimum" $ prop_minimum
        , testProperty "splitAt" $ prop_splitAt
        , testProperty "takeWhile" $ prop_takeWhile
        , testProperty "dropWhile" $ prop_dropWhile
        , testProperty "span" $ prop_span
        , testProperty "break" $ prop_break
        , testProperty "elem" $ prop_elem
        , testProperty "notElem" $ prop_notElem
        , testProperty "lookup" $ prop_lookup
        , testProperty "zip" $ prop_zip
        , testProperty "zip3" $ prop_zip3
        , testProperty "zipWith" $ prop_zipWith
        , testProperty "zipWith3" $ prop_zipWith3
        , testProperty "unzip" $ prop_unzip
        , testProperty "unzip3" $ prop_unzip3
        , testProperty "nub" $ prop_nub
        , testProperty "number" $ prop_number
        , testProperty "reshape" $ prop_reshape
        , testProperty "reshape2" $ prop_reshape2
        , testProperty "transpose" $ prop_transpose
        ]

tests_lifted :: Test
tests_lifted = testGroup "Lifted operations"
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
        , testProperty "Lifted groupWithKey" $ prop_map_groupWithKey
        , testProperty "Lifted sortWith" $ prop_map_sortWith
        , testProperty "Lifted sortWith length" $ prop_map_sortWith_length
        , testProperty "Lifted groupWithKey length" $ prop_map_groupWithKey_length
        , testProperty "Lifted length" $ prop_map_length
        , testProperty "Lifted length on [[(a,b)]]" $ prop_map_length_tuple
        , testProperty "Sortwith length nested" $ prop_sortWith_length_nest
        , testProperty "GroupWithKey length nested" $ prop_groupWithKey_length_nest
        , testProperty "Lift minimum" $ prop_map_minimum
        , testProperty "map (map minimum)" $ prop_map_map_minimum
        , testProperty "Lift maximum" $ prop_map_maximum
        , testProperty "map (map maximum)" $ prop_map_map_maximum
        , testProperty "map integer_to_double" $ prop_map_integer_to_double
        , testProperty "map tail" $ prop_map_tail
        , testProperty "map unzip" $ prop_map_unzip
        , testProperty "map reverse" $ prop_map_reverse
        , testProperty "map reverse [[]]" $ prop_map_reverse_nest
        , testProperty "map and" $ prop_map_and
        , testProperty "map (map and)" $ prop_map_map_and
        , testProperty "map sum" $ prop_map_sum
        , testProperty "map avg" $ prop_map_avg
        , testProperty "map (map sum)" $ prop_map_map_sum
        , testProperty "map or" $ prop_map_or
        , testProperty "map (map or)" $ prop_map_map_or
        , testProperty "map any zero" $ prop_map_any_zero
        , testProperty "map all zero" $ prop_map_all_zero
        , testProperty "map filter" $ prop_map_filter
        , testProperty "map append" $ prop_map_append
        , testProperty "map index" $ prop_map_index
        , testProperty "map index [[]]" $ prop_map_index_nest
        , testProperty "map init" $ prop_map_init
        , testProperty "map last" $ prop_map_last
        , testProperty "map null" $ prop_map_null
        , testProperty "map nub" $ prop_map_nub
        , testProperty "map snoc" $ prop_map_snoc
        , testProperty "map take" $ prop_map_take
        , testProperty "map drop" $ prop_map_drop
        , testProperty "map zip" $ prop_map_zip
        , testProperty "map takeWhile" $ prop_map_takeWhile
        , testProperty "map dropWhile" $ prop_map_dropWhile
        , testProperty "map span" $ prop_map_span
        , testProperty "map break" $ prop_map_break
        , testProperty "map number" $ prop_map_number
        , testProperty "map reshape" $ prop_map_reshape
        , testProperty "map reshape2" $ prop_map_reshape2
        -- , testProperty "map transpose" $ prop_map_transpose
        , testProperty "map sin" $ prop_map_trig_sin
        , testProperty "map cos" $ prop_map_trig_cos
        , testProperty "map tan" $ prop_map_trig_tan
        , testProperty "map asin" $ prop_map_trig_asin
        , testProperty "map acos" $ prop_map_trig_acos
        , testProperty "map atan" $ prop_map_trig_atan
        , testProperty "map log" $ prop_map_log
        , testProperty "map exp" $ prop_map_exp
        , testProperty "map sqrt" $ prop_map_sqrt
        ]

tests_combinators_hunit :: Test
tests_combinators_hunit = testGroup "HUnit combinators"
    [ testCase "hnegative_sum" hnegative_sum
    , testCase "hnegative_map_sum" hnegative_map_sum
    , testCase "hmap_transpose" hmap_transpose
    ]

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

prop_list_tuple_integer :: [(Integer, Integer)] -> Property
prop_list_tuple_integer = makeProp id id

prop_maybe_integer :: Maybe Integer -> Property
prop_maybe_integer = makeProp id id

prop_tuple_list_integer :: ([Integer], [Integer]) -> Property
prop_tuple_list_integer = makeProp id id

prop_either_integer :: Either Integer Integer -> Property
prop_either_integer = makeProp id id

prop_d0 :: D0 -> Property
prop_d0 = makeProp id id

prop_d1 :: D1 Integer -> Property
prop_d1 = makeProp id id

prop_d2 :: D2 Integer Integer -> Property
prop_d2 = makeProp id id

prop_d3 :: D3 -> Property
prop_d3 = makeProp id id

prop_d4 :: D4 Integer -> Property
prop_d4 = makeProp id id

prop_d5 :: D5 Integer -> Property
prop_d5 = makeProp id id

prop_d6 :: D6 Integer Integer Integer Integer Integer -> Property
prop_d6 = makeProp id id

-- * Equality, Boolean Logic and Ordering

prop_infix_and :: (Bool,Bool) -> Property
prop_infix_and = makeProp (uncurryQ (Q.&&)) (uncurry (&&))

prop_infix_map_and :: (Bool, [Bool]) -> Property
prop_infix_map_and = makeProp (\x -> Q.map ((Q.fst x) Q.&&) $ Q.snd x) (\(x,xs) -> map (x &&) xs)

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
prop_cond = makeProp (\b -> Q.cond b 0 1) (\b -> if b then (0 :: Integer) else 1)

prop_cond_tuples :: (Bool, (Integer, Integer)) -> Property
prop_cond_tuples = makeProp (\b -> Q.cond (Q.fst b) 
                                          (Q.pair (Q.fst $ Q.snd b) (Q.fst $ Q.snd b)) 
                                          (Q.pair (Q.snd $ Q.snd b) (Q.snd $ Q.snd b))) 
                            (\b -> if fst b 
                                   then (fst $ snd b, fst $ snd b) 
                                   else (snd $ snd b, snd $ snd b))

prop_cond_list_tuples :: (Bool, ([[Integer]], [[Integer]])) -> Property
prop_cond_list_tuples = makeProp (\b -> Q.cond (Q.fst b) 
                                               (Q.pair (Q.fst $ Q.snd b) (Q.fst $ Q.snd b)) 
                                               (Q.pair (Q.snd $ Q.snd b) (Q.snd $ Q.snd b))) 
                                 (\b -> if fst b 
                                        then (fst $ snd b, fst $ snd b) 
                                        else (snd $ snd b, snd $ snd b))

prop_map_cond :: [Bool] -> Property
prop_map_cond = makeProp (Q.map (\b -> Q.cond b (0 :: Q.Q Integer) 1)) 
                         (map (\b -> if b then 0 else 1))

prop_map_cond_tuples :: [Bool] -> Property
prop_map_cond_tuples = makeProp (Q.map (\b -> Q.cond b 
                                                     (Q.toQ (0, 10) :: Q.Q (Integer, Integer)) 
                                                     (Q.toQ (1, 11)))) 
                                (map (\b -> if b 
                                            then (0, 10) 
                                            else (1, 11)))

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
prop_left = makeProp (Q.left :: Q.Q Integer -> Q.Q (Either Integer Integer)) Left

prop_right :: Integer -> Property
prop_right = makeProp (Q.right :: Q.Q Integer -> Q.Q (Either Integer Integer)) Right

prop_isLeft :: Either Integer Integer -> Property
prop_isLeft = makeProp Q.isLeft (\e -> case e of {Left _ -> True; Right _ -> False;})

prop_isRight :: Either Integer Integer -> Property
prop_isRight = makeProp Q.isRight (\e -> case e of {Left _ -> False; Right _ -> True;})

prop_either :: Either Integer Integer -> Property
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

prop_map_cons :: (Integer, [[Integer]]) -> Property
prop_map_cons = makeProp (\x -> Q.map ((Q.fst x) Q.<|) $ Q.snd x) 
                         (\(x,xs) -> map (x:) xs)

prop_snoc :: ([Integer], Integer) -> Property
prop_snoc = makeProp (uncurryQ (Q.|>)) (\(a,b) -> a ++ [b])

prop_map_snoc :: ([Integer], [Integer]) -> Property
prop_map_snoc = makeProp (\z -> Q.map ((Q.fst z) Q.|>) (Q.snd z)) (\(a,b) -> map (\z -> a ++ [z]) b)

prop_singleton :: Integer -> Property
prop_singleton = makeProp Q.singleton (: [])

prop_head  :: [Integer] -> Property
prop_head  = makePropNotNull Q.head head

prop_tail  :: [Integer] -> Property
prop_tail  = makePropNotNull Q.tail tail

prop_last  :: [Integer] -> Property
prop_last  = makePropNotNull Q.last last

prop_map_last :: [[Integer]] -> Property
prop_map_last ps = and (map ((>0) . length) ps) ==> makeProp (Q.map Q.last) (map last) ps

prop_init  :: [Integer] -> Property
prop_init  = makePropNotNull Q.init init

prop_map_init  :: [[Integer]] -> Property
prop_map_init  ps = and (map ((>0) . length) ps)
    ==>
     makeProp (Q.map Q.init) (map init) ps

prop_the   :: (Int, Integer) -> Property
prop_the (n, i) =
  n > 0
  ==>
  let l = replicate n i in makeProp Q.head the l

prop_map_the :: [(Int, Integer)] -> Property
prop_map_the ps =
  let ps' = filter ((>0) . fst) ps in
  (length ps') > 0
  ==>
  let xss = map (\(n, i) -> replicate n i) ps' in
  makeProp (Q.map Q.head) (map the) xss

prop_map_tail :: [[Integer]] -> Property
prop_map_tail ps =
    and [length p > 0 | p <- ps]
    ==>
    makeProp (Q.map Q.tail) (map tail) ps

prop_index :: ([Integer], Integer)  -> Property
prop_index (l, i) =
        i > 0 && i < fromIntegral (length l)
    ==> makeProp (uncurryQ (Q.!!))
                 (\(a,b) -> a !! fromIntegral b)
                 (l, i)

prop_index_pair :: ([(Integer, [Integer])], Integer) -> Property
prop_index_pair (l, i) =
        i > 0 && i < fromIntegral (length l)               
    ==> makeProp (uncurryQ (Q.!!))
                 (\(a,b) -> a !! fromIntegral b)
                 (l, i)

prop_index_nest :: ([[Integer]], Integer)  -> Property
prop_index_nest (l, i) =
     i > 0 && i < fromIntegral (length l)
 ==> makeProp (uncurryQ (Q.!!))
              (\(a,b) -> a !! fromIntegral b)
              (l, i)

prop_map_index :: ([Integer], [Integer])  -> Property
prop_map_index (l, is) =
     and [i >= 0 && i < 2 * fromIntegral (length l) | i <-  is]
 ==> makeProp (\z -> Q.map (((Q.fst z) Q.++ (Q.fst z) Q.++ (Q.fst z)) Q.!!) (Q.snd z))
              (\(a,b) -> map ((a ++ a ++ a) !!) (map fromIntegral b))
              (l, is)

prop_map_index_nest :: ([[Integer]], [Integer])  -> Property
prop_map_index_nest (l, is) =
     and [i >= 0 && i < 3 * fromIntegral (length l) | i <-  is]
 ==> makeProp (\z -> Q.map (((Q.fst z) Q.++ (Q.fst z) Q.++ (Q.fst z)) Q.!!) (Q.snd z))
            (\(a,b) -> map ((a ++ a ++ a) !!) (map fromIntegral b))
            (l, is)

prop_take :: (Integer, [Integer]) -> Property
prop_take = makeProp (uncurryQ Q.take) (\(n,l) -> take (fromIntegral n) l)

prop_map_take :: (Integer, [[Integer]]) -> Property
prop_map_take = makeProp (\z -> Q.map (Q.take $ Q.fst z) $ Q.snd z) (\(n,l) -> map (take (fromIntegral n)) l)

prop_drop :: (Integer, [Integer]) -> Property
prop_drop = makeProp (uncurryQ Q.drop) (\(n,l) -> drop (fromIntegral n) l)

prop_map_drop :: (Integer, [[Integer]]) -> Property
prop_map_drop = makeProp (\z -> Q.map (Q.drop $ Q.fst z) $ Q.snd z) (\(n,l) -> map (drop (fromIntegral n)) l)

prop_takedrop :: (Integer, [Integer]) -> Property
prop_takedrop = makeProp takedrop_q takedrop
  where takedrop_q = \p -> Q.append ((Q.take (Q.fst p)) (Q.snd p)) ((Q.drop (Q.fst p)) (Q.snd p))
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
prop_append = makeProp (uncurryQ (Q.++)) (uncurry (++))

prop_append_nest :: ([[Integer]], [[Integer]]) -> Property
prop_append_nest = makeProp (uncurryQ (Q.append)) (\(a,b) -> a ++ b)

prop_map_append :: ([Integer], [[Integer]]) -> Property
prop_map_append = makeProp (\z -> Q.map (Q.fst z Q.++) (Q.snd z)) (\(a,b) -> map (a ++) b)

prop_filter :: [Integer] -> Property
prop_filter = makeProp (Q.filter (const $ Q.toQ True)) (filter $ const True)

prop_map_filter :: [[Integer]] -> Property
prop_map_filter = makeProp (Q.map (Q.filter (const $ Q.toQ True))) (map (filter $ const True))

prop_groupWith :: [Integer] -> Property
prop_groupWith = makeProp (Q.groupWith id) (groupWith id)

groupWithKey :: Ord b => (a -> b) -> [a] -> [(b, [a])]
groupWithKey p as = map (\g -> (the $ map p g, g)) $ groupWith p as

prop_groupWithKey :: [Integer] -> Property
prop_groupWithKey = makeProp (Q.groupWithKey id) (groupWithKey id)

prop_map_groupWith :: [[Integer]] -> Property
prop_map_groupWith = makeProp (Q.map (Q.groupWith id)) (map (groupWith id))

prop_map_groupWithKey :: [[Integer]] -> Property
prop_map_groupWithKey = makeProp (Q.map (Q.groupWithKey id)) (map (groupWithKey id))

prop_groupWith_length :: [[Integer]] -> Property
prop_groupWith_length = makeProp (Q.groupWith Q.length) (groupWith length)

prop_groupWithKey_length :: [[Integer]] -> Property
prop_groupWithKey_length = makeProp (Q.groupWithKey Q.length) (groupWithKey (fromIntegral . length))

prop_sortWith  :: [Integer] -> Property
prop_sortWith = makeProp (Q.sortWith id) (sortWith id)

prop_map_sortWith :: [[Integer]] -> Property
prop_map_sortWith = makeProp (Q.map (Q.sortWith id)) (map (sortWith id))

prop_map_sortWith_length :: [[[Integer]]] -> Property
prop_map_sortWith_length = makeProp (Q.map (Q.sortWith Q.length)) (map (sortWith length))

prop_map_groupWith_length :: [[[Integer]]] -> Property
prop_map_groupWith_length = makeProp (Q.map (Q.groupWith Q.length)) (map (groupWith length))

prop_map_groupWithKey_length :: [[[Integer]]] -> Property
prop_map_groupWithKey_length = makeProp (Q.map (Q.groupWithKey Q.length)) (map (groupWithKey (fromIntegral . length)))

prop_sortWith_length_nest  :: [[[Integer]]] -> Property
prop_sortWith_length_nest = makeProp (Q.sortWith Q.length) (sortWith length)

prop_groupWith_length_nest :: [[[Integer]]] -> Property
prop_groupWith_length_nest = makeProp (Q.groupWith Q.length) (groupWith length)

prop_groupWithKey_length_nest :: [[[Integer]]] -> Property
prop_groupWithKey_length_nest = makeProp (Q.groupWithKey Q.length) (groupWithKey (fromIntegral . length))

prop_null :: [Integer] -> Property
prop_null = makeProp Q.null null

prop_map_null :: [[Integer]] -> Property
prop_map_null = makeProp (Q.map Q.null) (map null)

prop_length :: [Integer] -> Property
prop_length = makeProp Q.length ((fromIntegral :: Int -> Integer) . length)

prop_length_tuple :: [(Integer, Integer)] -> Property
prop_length_tuple = makeProp Q.length (fromIntegral . length)

prop_map_length :: [[Integer]] -> Property
prop_map_length = makeProp (Q.map Q.length) (map (fromIntegral . length))

prop_map_minimum :: [[Integer]] -> Property
prop_map_minimum ps = and (map (\p -> length p > 0) ps)
        ==>
    makeProp (Q.map Q.minimum) (map (fromIntegral . minimum)) ps

prop_map_maximum :: [[Integer]] -> Property
prop_map_maximum ps = and (map (\p -> length p > 0) ps)
        ==>
    makeProp (Q.map Q.maximum) (map (fromIntegral . maximum)) ps

prop_map_map_minimum :: [[[Integer]]] -> Property
prop_map_map_minimum ps = and (map (and . map (\p -> length p > 0)) ps)
        ==>
    makeProp (Q.map (Q.map Q.minimum)) (map (map(fromIntegral . minimum))) ps

prop_map_map_maximum :: [[[Integer]]] -> Property
prop_map_map_maximum ps = and (map (and . map (\p -> length p > 0)) ps)
        ==>
    makeProp (Q.map (Q.map Q.maximum)) (map (map(fromIntegral . maximum))) ps


prop_map_length_tuple :: [[(Integer, Integer)]] -> Property
prop_map_length_tuple = makeProp (Q.map Q.length) (map (fromIntegral . length))

prop_reverse :: [Integer] -> Property
prop_reverse = makeProp Q.reverse reverse

prop_reverse_nest :: [[Integer]] -> Property
prop_reverse_nest = makeProp Q.reverse reverse

prop_map_reverse :: [[Integer]] -> Property
prop_map_reverse = makeProp (Q.map Q.reverse) (map reverse)

prop_map_reverse_nest :: [[[Integer]]] -> Property
prop_map_reverse_nest = makeProp (Q.map Q.reverse) (map reverse)

prop_and :: [Bool] -> Property
prop_and = makeProp Q.and and

prop_map_and :: [[Bool]] -> Property
prop_map_and = makeProp (Q.map Q.and) (map and)

prop_map_map_and :: [[[Bool]]] -> Property
prop_map_map_and = makeProp (Q.map (Q.map Q.and)) (map (map and))

prop_or :: [Bool] -> Property
prop_or = makeProp Q.or or

prop_map_or :: [[Bool]] -> Property
prop_map_or = makeProp (Q.map Q.or) (map or)

prop_map_map_or :: [[[Bool]]] -> Property
prop_map_map_or = makeProp (Q.map (Q.map Q.or)) (map (map or))

prop_any_zero :: [Integer] -> Property
prop_any_zero = makeProp (Q.any (Q.== 0)) (any (== 0))

prop_map_any_zero :: [[Integer]] -> Property
prop_map_any_zero = makeProp (Q.map (Q.any (Q.== 0))) (map (any (== 0)))

prop_all_zero :: [Integer] -> Property
prop_all_zero = makeProp (Q.all (Q.== 0)) (all (== 0))

prop_map_all_zero :: [[Integer]] -> Property
prop_map_all_zero = makeProp (Q.map (Q.all (Q.== 0))) (map (all (== 0)))

prop_sum_integer :: [Integer] -> Property
prop_sum_integer = makeProp Q.sum sum
                 
avgInt :: [Integer] -> Double
avgInt is = (realToFrac $ sum is) / (fromIntegral $ length is)

prop_avg_integer :: [Integer] -> Property
prop_avg_integer is = (not $ null is) ==> makeProp Q.avg avgInt is

prop_map_sum :: [[Integer]] -> Property
prop_map_sum = makeProp (Q.map Q.sum) (map sum)

prop_map_avg :: [[Integer]] -> Property
prop_map_avg is = (not $ any null is) ==> makeProp (Q.map Q.avg) (map avgInt) is

prop_map_map_sum :: [[[Integer]]] -> Property
prop_map_map_sum = makeProp (Q.map (Q.map Q.sum)) (map (map sum))

prop_map_map_avg :: [[[Integer]]] -> Property
prop_map_map_avg is = (not $ any (any null) is) ==> makeProp (Q.map (Q.map Q.avg)) (map (map avgInt))

prop_sum_double :: [Double] -> Property
prop_sum_double = makePropDouble Q.sum sum

avgDouble :: [Double] -> Double
avgDouble ds = sum ds / (fromIntegral $ length ds)

prop_avg_double :: [Double] -> Property
prop_avg_double ds = (not $ null ds) ==> makePropDouble Q.avg avgDouble ds

prop_concat :: [[Integer]] -> Property
prop_concat = makeProp Q.concat concat

prop_map_concat :: [[[Integer]]] -> Property
prop_map_concat = makeProp (Q.map Q.concat) (map concat)

prop_concatMap :: [Integer] -> Property
prop_concatMap = makeProp (Q.concatMap Q.singleton) (concatMap (: []))

prop_maximum :: [Integer] -> Property
prop_maximum = makePropNotNull Q.maximum maximum

prop_minimum :: [Integer] -> Property
prop_minimum = makePropNotNull Q.minimum minimum

prop_splitAt :: (Integer, [Integer]) -> Property
prop_splitAt = makeProp (uncurryQ Q.splitAt) (\(a,b) -> splitAt (fromIntegral a) b)

prop_takeWhile :: (Integer, [Integer]) -> Property
prop_takeWhile = makeProp (uncurryQ $ Q.takeWhile . (Q.==))
                          (uncurry  $   takeWhile . (==))

prop_dropWhile :: (Integer, [Integer]) -> Property
prop_dropWhile = makeProp (uncurryQ $ Q.dropWhile . (Q.==))
                          (uncurry  $   dropWhile . (==))

prop_map_takeWhile :: (Integer, [[Integer]]) -> Property
prop_map_takeWhile = makeProp (\z -> Q.map (Q.takeWhile (Q.fst z Q.==)) (Q.snd z))
                              (\z -> map (takeWhile (fst z ==)) (snd z))

prop_map_dropWhile :: (Integer, [[Integer]]) -> Property
prop_map_dropWhile = makeProp (\z -> Q.map (Q.dropWhile (Q.fst z Q.==)) (Q.snd z))
                              (\z -> map (dropWhile (fst z ==)) (snd z))

prop_span :: (Integer, [Integer]) -> Property
prop_span = makeProp (uncurryQ $ Q.span . (Q.==))
                     (uncurry   $   span . (==) . fromIntegral)

prop_map_span :: (Integer, [[Integer]]) -> Property
prop_map_span = makeProp (\z -> Q.map (Q.span ((Q.fst z) Q.==)) (Q.snd z))
                         (\z -> map (span (fst z ==)) (snd z))

prop_break :: (Integer, [Integer]) -> Property
prop_break = makeProp (uncurryQ $ Q.break . (Q.==))
                      (uncurry   $   break . (==) . fromIntegral)

prop_map_break :: (Integer, [[Integer]]) -> Property
prop_map_break = makeProp (\z -> Q.map (Q.break ((Q.fst z) Q.==)) (Q.snd z))
                          (\z -> map (break (fst z ==)) (snd z))

prop_elem :: (Integer, [Integer]) -> Property
prop_elem = makeProp (uncurryQ Q.elem)
                     (uncurry    elem)

prop_notElem :: (Integer, [Integer]) -> Property
prop_notElem = makeProp (uncurryQ Q.notElem)
                        (uncurry    notElem)

prop_lookup :: (Integer, [(Integer,Integer)]) -> Property
prop_lookup = makeProp (uncurryQ Q.lookup)
                       (uncurry    lookup)

prop_zip :: ([Integer], [Integer]) -> Property
prop_zip = makeProp (uncurryQ Q.zip) (uncurry zip)

prop_map_zip :: ([Integer], [[Integer]]) -> Property
prop_map_zip = makeProp (\z -> Q.map (Q.zip $ Q.fst z) $ Q.snd z) (\(x, y) -> map (zip x) y)

prop_zipWith :: ([Integer], [Integer]) -> Property
prop_zipWith = makeProp (uncurryQ $ Q.zipWith (+)) (uncurry $ zipWith (+))

prop_unzip :: [(Integer, Integer)] -> Property
prop_unzip = makeProp Q.unzip unzip

prop_map_unzip :: [[(Integer, Integer)]] -> Property
prop_map_unzip = makeProp (Q.map Q.unzip) (map unzip)

prop_zip3 :: ([Integer], [Integer],[Integer]) -> Property
prop_zip3 = makeProp (\q -> (case Q.view q of (as,bs,cs) -> Q.zip3 as bs cs))
                     (\(as,bs,cs) -> zip3 as bs cs)

prop_zipWith3 :: ([Integer], [Integer],[Integer]) -> Property
prop_zipWith3 = makeProp (\q -> (case Q.view q of (as,bs,cs) -> Q.zipWith3 (\a b c -> a + b + c) as bs cs))
                         (\(as,bs,cs) -> zipWith3 (\a b c -> a + b + c) as bs cs)

prop_unzip3 :: [(Integer, Integer, Integer)] -> Property
prop_unzip3 = makeProp Q.unzip3 unzip3

prop_nub :: [Integer] -> Property
prop_nub = makeProp Q.nub nub

prop_map_nub :: [[(Integer, Integer)]] -> Property
prop_map_nub = makeProp (Q.map Q.nub) (map nub)

-- * Tuples

prop_fst :: (Integer, Integer) -> Property
prop_fst = makeProp Q.fst fst

prop_fst_nested :: ([Integer], [Integer]) -> Property
prop_fst_nested = makeProp Q.fst fst

prop_map_fst :: [(Integer, Integer)] -> Property
prop_map_fst = makeProp (Q.map Q.fst) (map fst)

prop_snd :: (Integer, Integer) -> Property
prop_snd = makeProp Q.snd snd

prop_map_snd :: [(Integer, Integer)] -> Property
prop_map_snd = makeProp (Q.map Q.snd) (map snd)

prop_snd_nested :: ([Integer], [Integer]) -> Property
prop_snd_nested = makeProp Q.snd snd

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

prop_integer_to_double_arith :: (Integer, Double) -> Property
prop_integer_to_double_arith = makePropDouble (\x -> (Q.integerToDouble (Q.fst x)) + (Q.snd x))
                                              (\(i, d) -> fromInteger i + d)

prop_map_integer_to_double :: [Integer] -> Property
prop_map_integer_to_double = makePropListDouble (Q.map Q.integerToDouble) (map fromInteger)

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

prop_trig_sin :: Double -> Property
prop_trig_sin = makePropDouble Q.sin sin

prop_trig_cos :: Double -> Property
prop_trig_cos = makePropDouble Q.cos cos

prop_trig_tan :: Double -> Property
prop_trig_tan = makePropDouble Q.tan tan

prop_exp :: Double -> Property
prop_exp = makePropDouble Q.exp exp

prop_log :: Double -> Property
prop_log d = d > 0 ==> makePropDouble Q.log log d

prop_sqrt :: Double -> Property
prop_sqrt d = d > 0 ==> makePropDouble Q.sqrt sqrt d

arc :: Double -> Bool
arc d = d >= -1 && d <= 1

prop_trig_asin :: Double -> Property
prop_trig_asin d = arc d ==>  makePropDouble Q.asin asin d

prop_trig_acos :: Double -> Property
prop_trig_acos d = arc d ==> makePropDouble Q.acos acos d

prop_trig_atan :: Double -> Property
prop_trig_atan = makePropDouble Q.atan atan

prop_number :: [Integer] -> Property
prop_number = makeProp (Q.map Q.snd . Q.number) (\xs -> map snd $ zip xs [1..])

prop_map_number :: [[Integer]] -> Property
prop_map_number = makeProp (Q.map (Q.map Q.snd . Q.number))
                            (map (\xs -> map snd $ zip xs [1..]))

prop_transpose :: [[Integer]] -> Property
prop_transpose = makeProp Q.transpose transpose

{-
prop_map_transpose :: [[[Integer]]] -> Property
prop_map_transpose xss = 
    (all (not . null) (xss :: [[[Integer]]])
    &&
    and (map (all (not . null)) xss))
    ==> makeProp (Q.map Q.transpose) (map transpose)
-}

reshape :: Int -> [a] -> [[a]]
reshape _ [] = []
reshape i xs = take i xs : reshape i (drop i xs)

prop_reshape :: [Integer] -> Property
prop_reshape = makeProp (Q.reshape 5) (reshape 5)

prop_reshape2 :: [Integer] -> Property
prop_reshape2 = makeProp (Q.reshape 2) (reshape 2)
             
prop_map_reshape :: [[Integer]] -> Property
prop_map_reshape = makeProp (Q.map (Q.reshape 8)) (map (reshape 8))

prop_map_reshape2 :: [[Integer]] -> Property
prop_map_reshape2 = makeProp (Q.map (Q.reshape 2)) (map (reshape 2))

prop_map_trig_sin :: [Double] -> Property
prop_map_trig_sin = makePropListDouble (Q.map Q.sin) (map sin)

prop_map_trig_cos :: [Double] -> Property
prop_map_trig_cos = makePropListDouble (Q.map Q.cos) (map cos)

prop_map_trig_tan :: [Double] -> Property
prop_map_trig_tan = makePropListDouble (Q.map Q.tan) (map tan)

prop_map_trig_asin :: [Double] -> Property
prop_map_trig_asin ds = all arc ds ==> makePropListDouble (Q.map Q.asin) (map asin) ds

prop_map_trig_acos :: [Double] -> Property
prop_map_trig_acos ds = all arc ds ==> makePropListDouble (Q.map Q.acos) (map acos) ds

prop_map_trig_atan :: [Double] -> Property
prop_map_trig_atan = makePropListDouble (Q.map Q.atan) (map atan)

prop_map_exp :: [Double] -> Property
prop_map_exp = makePropListDouble (Q.map Q.exp) (map exp)

prop_map_log :: [Double] -> Property
prop_map_log ds = all (> 0) ds ==> makePropListDouble (Q.map Q.log) (map log) ds

prop_map_sqrt :: [Double] -> Property
prop_map_sqrt ds = all (> 0) ds ==> makePropListDouble (Q.map Q.sqrt) (map sqrt) ds
                   

hnegative_sum :: Assertion
hnegative_sum = makeEqAssertion "hnegative_sum" (Q.sum (Q.toQ xs)) (sum xs)
  where
    xs :: [Integer]
    xs = [-1, -4, -5, 2]

hnegative_map_sum :: Assertion
hnegative_map_sum = makeEqAssertion "hnegative_map_sum" 
                                    (Q.map Q.sum (Q.toQ xss)) 
                                    (map sum xss)
  where
    xss :: [[Integer]]
    xss = [[10, 20, 30], [-10, -20, -30], [], [0]]

hmap_transpose :: Assertion
hmap_transpose = makeEqAssertion "hmap_transpose" (Q.map Q.transpose (Q.toQ xss)) res
  where
    xss :: [[[Integer]]]
    xss = [ [ [10, 20, 30]
            , [40, 50, 60]]
          , [ [100, 200]
            , [300, 400]
            , [500, 600]]
          ]

    res :: [[[Integer]]]
    res = [ [ [10, 40]
            , [20, 50]
            , [30, 60]
            ]
          , [ [100, 300, 500]
            , [200, 400, 600]
            ]
          ]
