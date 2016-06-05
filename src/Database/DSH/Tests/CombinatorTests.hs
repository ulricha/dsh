{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE ViewPatterns          #-}

-- | Tests on individual query combinators.
module Database.DSH.Tests.CombinatorTests
    ( typeTests
    , booleanTests
    , tupleTests
    , numericTests
    , maybeTests
    , eitherTests
    , listTests
    , liftedTests
    , distTests
    , hunitCombinatorTests
    , otherTests
    ) where


import qualified Data.Decimal              as D
import           Data.Either
import           Data.List
import           Data.Maybe
import qualified Data.Scientific           as S
import           Data.Text                 (Text)
import qualified Data.Time.Calendar        as C
import           Data.Word
import           GHC.Exts

import           Test.QuickCheck
import           Test.Tasty
import qualified Test.Tasty.HUnit          as TH

import qualified Database.DSH              as Q
import           Database.DSH.Backend
import           Database.DSH.Compiler
import           Database.DSH.Tests.Common

{-# ANN module "HLint: ignore Use camelCase" #-}
{-# ANN module "HLint: ignore Avoid lambda" #-}

{-
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

-}

typeTests :: (BackendVector b, VectorLang v) => DSHTestTree v b
typeTests codeGen conn = testGroup "Supported Types"
  [ testPropertyConn codeGen conn "()"                        prop_unit
  , testPropertyConn codeGen conn "Bool"                      prop_bool
  , testPropertyConn codeGen conn "Char"                      prop_char
  , testPropertyConn codeGen conn "Text"                      prop_text
  , testPropertyConn codeGen conn "Day"                       prop_day
  , testPropertyConn codeGen conn "Decimal"                   prop_decimal
  , testPropertyConn codeGen conn "Scientific"                prop_scientific
  , testPropertyConn codeGen conn "Integer"                   prop_integer
  , testPropertyConn codeGen conn "Double"                    prop_double
  , testPropertyConn codeGen conn "[Integer]"                 prop_list_integer_1
  , testPropertyConn codeGen conn "[[Integer]]"               prop_list_integer_2
  , testPropertyConn codeGen conn "[[[Integer]]]"             prop_list_integer_3
  , testPropertyConn codeGen conn "[(Integer, Integer)]"      prop_list_tuple_integer
  , testPropertyConn codeGen conn "([], [])"                  prop_tuple_list_integer2
  , testPropertyConn codeGen conn "([], [], [])"              prop_tuple_list_integer3
  , testPropertyConn codeGen conn "(,[])"                     prop_tuple_integer_list
  , testPropertyConn codeGen conn "(,[],)"                    prop_tuple_integer_list_integer
  , testPropertyConn codeGen conn "Maybe Integer"             prop_maybe_integer
  , testPropertyConn codeGen conn "Either Integer Integer"    prop_either_integer
  , testPropertyConn codeGen conn "(Int, Int, Int, Int)"      prop_tuple4
  , testPropertyConn codeGen conn "(Int, Int, Int, Int, Int)" prop_tuple5
{-
  , testProperty "D0" $ prop_d0
  , testProperty "D1" $ prop_d1
  , testProperty "D2" $ prop_d2
  , testProperty "D3" $ prop_d3
  , testProperty "D4" $ prop_d4
  , testProperty "D5" $ prop_d5
  , testProperty "D6" $ prop_d6
-}
  ]

booleanTests :: (BackendVector b, VectorLang v) => DSHTestTree v b
booleanTests codeGen conn = testGroup "Equality, Boolean Logic and Ordering"
    [ testPropertyConn codeGen conn "&&"                              prop_infix_and
    , testPropertyConn codeGen conn "||"                              prop_infix_or
    , testPropertyConn codeGen conn "not"                             prop_not
    , testPropertyConn codeGen conn "eq"                              prop_eq
    , testPropertyConn codeGen conn "neq"                             prop_neq
    , testPropertyConn codeGen conn "cond"                            prop_cond
    , testPropertyConn codeGen conn "cond tuples"                     prop_cond_tuples
    -- FIXME test fails but is somewhat hard to analyze. Should be fixed anyway some time.
    -- , testPropertyConn codeGen conn "cond ([[Integer]], [[Integer]])" prop_cond_list_tuples
    , testPropertyConn codeGen conn "lt"                              prop_lt
    , testPropertyConn codeGen conn "lte"                             prop_lte
    , testPropertyConn codeGen conn "gt"                              prop_gt
    , testPropertyConn codeGen conn "gte"                             prop_gte
    , testPropertyConn codeGen conn "min_integer"                     prop_min_integer
    , testPropertyConn codeGen conn "min_double"                      prop_min_double
    , testPropertyConn codeGen conn "max_integer"                     prop_max_integer
    , testPropertyConn codeGen conn "max_double"                      prop_max_double
    ]

tupleTests :: (BackendVector b, VectorLang v) => DSHTestTree v b
tupleTests codeGen conn = testGroup "Tuples"
    [ testPropertyConn codeGen conn "fst"          prop_fst
    , testPropertyConn codeGen conn "snd"          prop_snd
    , testPropertyConn codeGen conn "fst ([], [])" prop_fst_nested
    , testPropertyConn codeGen conn "snd ([], [])" prop_snd_nested
    , testPropertyConn codeGen conn "tup3_1"       prop_tup3_1
    , testPropertyConn codeGen conn "tup3_2"       prop_tup3_2
    , testPropertyConn codeGen conn "tup3_3"       prop_tup3_3
    , testPropertyConn codeGen conn "tup4_2"       prop_tup4_2
    , testPropertyConn codeGen conn "tup4_4"       prop_tup4_4
    , testPropertyConn codeGen conn "tup3_nested"  prop_tup3_nested
    , testPropertyConn codeGen conn "tup4_tup3"    prop_tup4_tup3
    , testPropertyConn codeGen conn "agg tuple"    prop_agg_tuple
    ]

numericTests :: (BackendVector b, VectorLang v) => DSHTestTree v b
numericTests codeGen conn = testGroup "Numerics"
    [ testPropertyConn codeGen conn "add_integer"         prop_add_integer
    , testPropertyConn codeGen conn "add_integer_sums"    prop_add_integer_sums
    , testPropertyConn codeGen conn "add_double"          prop_add_double
    , testPropertyConn codeGen conn "mul_integer"         prop_mul_integer
    , testPropertyConn codeGen conn "mul_double"          prop_mul_double
    , testPropertyConn codeGen conn "div_double"          prop_div_double
    , testPropertyConn codeGen conn "integer_to_double"   prop_integer_to_double
    , testPropertyConn codeGen conn "integer_to_double_+" prop_integer_to_double_arith
    , testPropertyConn codeGen conn "abs_integer"         prop_abs_integer
    , testPropertyConn codeGen conn "abs_double"          prop_abs_double
    , testPropertyConn codeGen conn "signum_integer"      prop_signum_integer
    , testPropertyConn codeGen conn "signum_double"       prop_signum_double
    , testPropertyConn codeGen conn "negate_integer"      prop_negate_integer
    , testPropertyConn codeGen conn "negate_double"       prop_negate_double
    , testPropertyConn codeGen conn "trig_sin"            prop_trig_sin
    , testPropertyConn codeGen conn "trig_cos"            prop_trig_cos
    , testPropertyConn codeGen conn "trig_tan"            prop_trig_tan
    , testPropertyConn codeGen conn "trig_asin"           prop_trig_asin
    , testPropertyConn codeGen conn "trig_acos"           prop_trig_acos
    , testPropertyConn codeGen conn "trig_atan"           prop_trig_atan
    , testPropertyConn codeGen conn "sqrt"                prop_sqrt
    , testPropertyConn codeGen conn "log"                 prop_log
    , testPropertyConn codeGen conn "exp"                 prop_exp
    , testPropertyConn codeGen conn "rem"                 prop_rem
    ]

maybeTests :: (BackendVector b, VectorLang v) => DSHTestTree v b
maybeTests codeGen conn = testGroup "Maybe"
    [ testPropertyConn codeGen conn "maybe"       prop_maybe
    , testPropertyConn codeGen conn "just"        prop_just
    , testPropertyConn codeGen conn "isJust"      prop_isJust
    , testPropertyConn codeGen conn "isNothing"   prop_isNothing
    , testPropertyConn codeGen conn "fromJust"    prop_fromJust
    , testPropertyConn codeGen conn "fromMaybe"   prop_fromMaybe
    , testPropertyConn codeGen conn "listToMaybe" prop_listToMaybe
    , testPropertyConn codeGen conn "maybeToList" prop_maybeToList
    , testPropertyConn codeGen conn "catMaybes"   prop_catMaybes
    , testPropertyConn codeGen conn "mapMaybe"    prop_mapMaybe
    ]

eitherTests :: (BackendVector b, VectorLang v) => DSHTestTree v b
eitherTests codeGen conn = testGroup "Either"
    [ testPropertyConn codeGen conn "left"             prop_left
    , testPropertyConn codeGen conn "right"            prop_right
    , testPropertyConn codeGen conn "isLeft"           prop_isLeft
    , testPropertyConn codeGen conn "isRight"          prop_isRight
    , testPropertyConn codeGen conn "either"           prop_either
    , testPropertyConn codeGen conn "lefts"            prop_lefts
    , testPropertyConn codeGen conn "rights"           prop_rights
    , testPropertyConn codeGen conn "partitionEithers" prop_partitionEithers
    ]

listTests :: (BackendVector b, VectorLang v) => DSHTestTree v b
listTests codeGen conn = testGroup "Lists"
    [ testPropertyConn codeGen conn "singleton" prop_singleton
    , testPropertyConn codeGen conn "head"                         prop_head
    , testPropertyConn codeGen conn "tail"                         prop_tail
    , testPropertyConn codeGen conn "cons"                         prop_cons
    , testPropertyConn codeGen conn "snoc"                         prop_snoc
    , testPropertyConn codeGen conn "take"                         prop_take
    , testPropertyConn codeGen conn "drop"                         prop_drop
    , testPropertyConn codeGen conn "take ++ drop"                 prop_takedrop
    , testPropertyConn codeGen conn "map"                          prop_map
    , testPropertyConn codeGen conn "filter"                       prop_filter
    , testPropertyConn codeGen conn "filter > 42"                  prop_filter_gt
    , testPropertyConn codeGen conn "filter > 42 (,[])"            prop_filter_gt_nested
    , testPropertyConn codeGen conn "the"                          prop_the
    , testPropertyConn codeGen conn "last"                         prop_last
    , testPropertyConn codeGen conn "init"                         prop_init
    , testPropertyConn codeGen conn "null"                         prop_null
    , testPropertyConn codeGen conn "length"                       prop_length
    , testPropertyConn codeGen conn "length tuple list"            prop_length_tuple
    , testPropertyConn codeGen conn "index [Integer]"              prop_index
    , testPropertyConn codeGen conn "index [(Integer, [Integer])]" prop_index_pair
    , testPropertyConn codeGen conn "index [[]]"                   prop_index_nest
    , testPropertyConn codeGen conn "reverse"                      prop_reverse
    , testPropertyConn codeGen conn "reverse [[]]"                 prop_reverse_nest
    , testPropertyConn codeGen conn "append"                       prop_append
    , testPropertyConn codeGen conn "append nest"                  prop_append_nest
    , testPropertyConn codeGen conn "groupWith"                    prop_groupWith
    , testPropertyConn codeGen conn "groupWithKey"                 prop_groupWithKey
    , testPropertyConn codeGen conn "groupWith length"             prop_groupWith_length
    , testPropertyConn codeGen conn "groupWithKey length"          prop_groupWithKey_length
    , testPropertyConn codeGen conn "groupWith length nested"      prop_groupWith_length_nest
    , testPropertyConn codeGen conn "groupWithKey length nested"   prop_groupWithKey_length_nest
    , testPropertyConn codeGen conn "groupagg sum"                 prop_groupagg_sum
    , testPropertyConn codeGen conn "groupagg (sum, length)"       prop_groupagg_sum_length
    , testPropertyConn codeGen conn "groupagg key  (sum, length)"  prop_groupaggkey_sum_length
    , testPropertyConn codeGen conn "groupagg (sum, length, max)"  prop_groupagg_sum_length_max
    , testPropertyConn codeGen conn "groupagg key sum"             prop_groupaggkey_sum
    , testPropertyConn codeGen conn "groupagg sum exp"             prop_groupagg_sum_exp
    , testPropertyConn codeGen conn "groupagg length"              prop_groupagg_length
    , testPropertyConn codeGen conn "groupagg minimum"             prop_groupagg_minimum
    , testPropertyConn codeGen conn "groupagg maximum"             prop_groupagg_maximum
    , testPropertyConn codeGen conn "groupagg avg"                 prop_groupagg_avg
    , testPropertyConn codeGen conn "sortWith"                     prop_sortWith
    , testPropertyConn codeGen conn "sortWith [(,)]"               prop_sortWith_pair
    , testPropertyConn codeGen conn "sortWith [(Char,)]"           prop_sortWith_pair_stable
    , testPropertyConn codeGen conn "sortWith [(,[])]"             prop_sortWith_nest
    , testPropertyConn codeGen conn "Sortwith length nested"       prop_sortWith_length_nest
    , testPropertyConn codeGen conn "and"                          prop_and
    , testPropertyConn codeGen conn "or"                           prop_or
    , testPropertyConn codeGen conn "any_zero"                     prop_any_zero
    , testPropertyConn codeGen conn "all_zero"                     prop_all_zero
    , testPropertyConn codeGen conn "sum_integer"                  prop_sum_integer
    , testPropertyConn codeGen conn "sum_double"                   prop_sum_double
    , testPropertyConn codeGen conn "avg_double"                   prop_avg_double
    , testPropertyConn codeGen conn "concat"                       prop_concat
    , testPropertyConn codeGen conn "concatMap"                    prop_concatMap
    , testPropertyConn codeGen conn "maximum"                      prop_maximum
    , testPropertyConn codeGen conn "minimum"                      prop_minimum
    , testPropertyConn codeGen conn "splitAt"                      prop_splitAt
    , testPropertyConn codeGen conn "takeWhile"                    prop_takeWhile
    , testPropertyConn codeGen conn "dropWhile"                    prop_dropWhile
    , testPropertyConn codeGen conn "span"                         prop_span
    , testPropertyConn codeGen conn "break"                        prop_break
    , testPropertyConn codeGen conn "elem"                         prop_elem
    , testPropertyConn codeGen conn "notElem"                      prop_notElem
    , testPropertyConn codeGen conn "lookup"                       prop_lookup
    , testPropertyConn codeGen conn "zip"                          prop_zip
    , testPropertyConn codeGen conn "zip tuple1"                   prop_zip_tuple1
    , testPropertyConn codeGen conn "zip tuple2"                   prop_zip_tuple2
    , testPropertyConn codeGen conn "zip nested"                   prop_zip_nested
    , testPropertyConn codeGen conn "zip3"                         prop_zip3
    , testPropertyConn codeGen conn "zipWith"                      prop_zipWith
    , testPropertyConn codeGen conn "zipWith3"                     prop_zipWith3
    , testPropertyConn codeGen conn "unzip"                        prop_unzip
    , testPropertyConn codeGen conn "unzip3"                       prop_unzip3
    , testPropertyConn codeGen conn "nub"                          prop_nub
    , testPropertyConn codeGen conn "number"                       prop_number
    ]

liftedTests :: (BackendVector b, VectorLang v) => DSHTestTree v b
liftedTests codeGen conn = testGroup "Lifted operations"
    [ testPropertyConn codeGen conn "Lifted &&"                             prop_infix_map_and
    , testPropertyConn codeGen conn "Lifted ||"                             prop_infix_map_or
    , testPropertyConn codeGen conn "Lifted not"                            prop_map_not
    , testPropertyConn codeGen conn "Lifted eq"                             prop_map_eq
    , testPropertyConn codeGen conn "Lifted neq"                            prop_map_neq
    , testPropertyConn codeGen conn "Lifted cond"                           prop_map_cond
    , testPropertyConn codeGen conn "Lifted cond tuples"                    prop_map_cond_tuples
    , testPropertyConn codeGen conn "Lifted cond + concat"                  prop_concatmapcond
    , testPropertyConn codeGen conn "Lifted lt"                             prop_map_lt
    , testPropertyConn codeGen conn "Lifted lte"                            prop_map_lte
    , testPropertyConn codeGen conn "Lifted gt"                             prop_map_gt
    , testPropertyConn codeGen conn "Lifted gte"                            prop_map_gte
    , testPropertyConn codeGen conn "Lifted cons"                           prop_map_cons
    , testPropertyConn codeGen conn "Lifted concat"                         prop_map_concat
    , testPropertyConn codeGen conn "Lifted fst"                            prop_map_fst
    , testPropertyConn codeGen conn "Lifted snd"                            prop_map_snd
    , testPropertyConn codeGen conn "Lifted the"                            prop_map_the
    , testPropertyConn codeGen conn "map (map (*2))"                        prop_map_map_mul
    , testPropertyConn codeGen conn "map (map (map (*2)))"                  prop_map_map_map_mul
    , testPropertyConn codeGen conn "map (\\x -> map (\\y -> x + y) ..) .." prop_map_map_add
    , testPropertyConn codeGen conn "map groupWith"                         prop_map_groupWith
    , testPropertyConn codeGen conn "map groupWith rem 10"                  prop_map_groupWith_rem
    , testPropertyConn codeGen conn "map groupWithKey"                      prop_map_groupWithKey
    , testPropertyConn codeGen conn "map groupagg (sum, length)"            prop_map_groupagg_sum_length
    , testPropertyConn codeGen conn "map groupagg key  (sum, length)"       prop_map_groupaggkey_sum_length
    , testPropertyConn codeGen conn "map groupagg (sum, length, max)"       prop_map_groupagg_sum_length_max
    , testPropertyConn codeGen conn "map groupagg sum"                      prop_map_groupagg_sum
    , testPropertyConn codeGen conn "map groupagg key sum"                  prop_map_groupaggkey_sum
    , testPropertyConn codeGen conn "map groupagg sum exp"                  prop_map_groupagg_sum_exp
    , testPropertyConn codeGen conn "map groupagg length"                   prop_map_groupagg_length
    , testPropertyConn codeGen conn "map groupagg minimum"                  prop_map_groupagg_minimum
    , testPropertyConn codeGen conn "map groupagg maximum"                  prop_map_groupagg_maximum
    , testPropertyConn codeGen conn "Lifted sortWith"                       prop_map_sortWith
    , testPropertyConn codeGen conn "Lifted sortWith [(,)]"                 prop_map_sortWith_pair
    , testPropertyConn codeGen conn "Lifted sortWith [(,[])]"               prop_map_sortWith_nest
    , testPropertyConn codeGen conn "Lifted sortWith length"                prop_map_sortWith_length
    , testPropertyConn codeGen conn "Lifted groupWithKey length"            prop_map_groupWithKey_length
    , testPropertyConn codeGen conn "Lifted length"                         prop_map_length
    , testPropertyConn codeGen conn "Lifted length on [[(a,b)]]"            prop_map_length_tuple
    , testPropertyConn codeGen conn "Lift minimum"                          prop_map_minimum
    , testPropertyConn codeGen conn "map (map minimum)"                     prop_map_map_minimum
    , testPropertyConn codeGen conn "Lift maximum"                          prop_map_maximum
    , testPropertyConn codeGen conn "map (map maximum)"                     prop_map_map_maximum
    , testPropertyConn codeGen conn "map integer_to_double"                 prop_map_integer_to_double
    , testPropertyConn codeGen conn "map tail"                              prop_map_tail
    , testPropertyConn codeGen conn "map unzip"                             prop_map_unzip
    , testPropertyConn codeGen conn "map reverse"                           prop_map_reverse
    , testPropertyConn codeGen conn "map reverse [[]]"                      prop_map_reverse_nest
    , testPropertyConn codeGen conn "map and"                               prop_map_and
    , testPropertyConn codeGen conn "map (map and)"                         prop_map_map_and
    , testPropertyConn codeGen conn "map sum"                               prop_map_sum
    , testPropertyConn codeGen conn "map avg"                               prop_map_avg
    , testPropertyConn codeGen conn "map (map sum)"                         prop_map_map_sum
    , testPropertyConn codeGen conn "map or"                                prop_map_or
    , testPropertyConn codeGen conn "map (map or)"                          prop_map_map_or
    , testPropertyConn codeGen conn "map any zero"                          prop_map_any_zero
    , testPropertyConn codeGen conn "map all zero"                          prop_map_all_zero
    , testPropertyConn codeGen conn "map filter"                            prop_map_filter
    , testPropertyConn codeGen conn "map filter > 42"                       prop_map_filter_gt
    , testPropertyConn codeGen conn "map filter > 42 (,[])"                 prop_map_filter_gt_nested
    , testPropertyConn codeGen conn "map append"                            prop_map_append
    , testPropertyConn codeGen conn "map index"                             prop_map_index
    , testPropertyConn codeGen conn "map index2"                            prop_map_index2
    , testPropertyConn codeGen conn "map index [[]]"                        prop_map_index_nest
    , testPropertyConn codeGen conn "map init"                              prop_map_init
    , testPropertyConn codeGen conn "map last"                              prop_map_last
    , testPropertyConn codeGen conn "map null"                              prop_map_null
    , testPropertyConn codeGen conn "map nub"                               prop_map_nub
    , testPropertyConn codeGen conn "map snoc"                              prop_map_snoc
    , testPropertyConn codeGen conn "map take"                              prop_map_take
    , testPropertyConn codeGen conn "map drop"                              prop_map_drop
    , testPropertyConn codeGen conn "map zip"                               prop_map_zip
    , testPropertyConn codeGen conn "map takeWhile"                         prop_map_takeWhile
    , testPropertyConn codeGen conn "map dropWhile"                         prop_map_dropWhile
    , testPropertyConn codeGen conn "map span"                              prop_map_span
    , testPropertyConn codeGen conn "map break"                             prop_map_break
    , testPropertyConn codeGen conn "map number"                            prop_map_number
    , testPropertyConn codeGen conn "map sin"                               prop_map_trig_sin
    , testPropertyConn codeGen conn "map cos"                               prop_map_trig_cos
    , testPropertyConn codeGen conn "map tan"                               prop_map_trig_tan
    , testPropertyConn codeGen conn "map asin"                              prop_map_trig_asin
    , testPropertyConn codeGen conn "map acos"                              prop_map_trig_acos
    , testPropertyConn codeGen conn "map atan"                              prop_map_trig_atan
    , testPropertyConn codeGen conn "map log"                               prop_map_log
    , testPropertyConn codeGen conn "map exp"                               prop_map_exp
    , testPropertyConn codeGen conn "map sqrt"                              prop_map_sqrt
    , testPropertyConn codeGen conn "map rem"                               prop_map_rem
    ]

distTests :: (BackendVector b, VectorLang v) => DSHTestTree v b
distTests codeGen conn = testGroup "Value replication"
    [ testPropertyConn codeGen conn "dist scalar" prop_dist_scalar
    , testPropertyConn codeGen conn "dist list1" prop_dist_list1
    , testPropertyConn codeGen conn "dist list2" prop_dist_list2
    , TH.testCase "dist lift" (test_dist_lift codeGen conn)
    ]

otherTests :: (BackendVector b, VectorLang v) => DSHTestTree v b
otherTests codeGen conn = testGroup "Combinations of operators"
    [ testPropertyConn codeGen conn "map elem + sort" prop_elem_sort
    , testPropertyConn codeGen conn "filter elem + sort" prop_elem_sort2
    , testPropertyConn codeGen conn "length . nub" prop_nub_length
    , testPropertyConn codeGen conn "map (length . nub)" prop_map_nub_length
    ]

hunitCombinatorTests :: (BackendVector b, VectorLang v) => DSHTestTree v b
hunitCombinatorTests codeGen conn = testGroup "HUnit combinators"
    [ TH.testCase "hnegative_sum"     (hnegative_sum codeGen conn)
    , TH.testCase "hnegative_map_sum" (hnegative_map_sum codeGen conn)
    ]

-- * Supported Types

prop_unit :: (BackendVector b, VectorLang v) => () -> DSHProperty v b
prop_unit = makePropEq id id

prop_bool :: (BackendVector b, VectorLang v) => Bool -> DSHProperty v b
prop_bool = makePropEq id id

prop_integer :: (BackendVector b, VectorLang v) => Integer -> DSHProperty v b
prop_integer = makePropEq id id

prop_double :: (BackendVector b, VectorLang v) => Fixed Double -> DSHProperty v b
prop_double d = makePropDouble id id (getFixed d)

prop_char :: (BackendVector b, VectorLang v) => Char -> DSHProperty v b
prop_char c codeGen conn = c /= '\0' ==> makePropEq id id c codeGen conn

prop_text :: (BackendVector b, VectorLang v) => Text -> DSHProperty v b
prop_text t = makePropEq id id (filterNullChar t)

prop_day :: (BackendVector b, VectorLang v) => C.Day -> DSHProperty v b
prop_day = makePropEq id id

prop_decimal :: (BackendVector b, VectorLang v) => (Positive Word8, Integer) -> DSHProperty v b
prop_decimal (p, m) = makePropEq id id (D.Decimal (getPositive p) m)

prop_scientific :: (BackendVector b, VectorLang v) => (Integer, Int) -> DSHProperty v b
prop_scientific (p, m) = makePropEq id id (S.scientific p m)

prop_list_integer_1 :: (BackendVector b, VectorLang v) => [Integer] -> DSHProperty v b
prop_list_integer_1 = makePropEq id id

prop_list_integer_2 :: (BackendVector b, VectorLang v) => [[Integer]] -> DSHProperty v b
prop_list_integer_2 = makePropEq id id

prop_list_integer_3 :: (BackendVector b, VectorLang v) => [[[Integer]]] -> DSHProperty v b
prop_list_integer_3 = makePropEq id id

prop_list_tuple_integer :: (BackendVector b, VectorLang v) => [(Integer, Integer)] -> DSHProperty v b
prop_list_tuple_integer = makePropEq id id

prop_maybe_integer :: (BackendVector b, VectorLang v) => Maybe Integer -> DSHProperty v b
prop_maybe_integer = makePropEq id id

prop_tuple_list_integer2 :: (BackendVector b, VectorLang v) => ([Integer], [Integer]) -> DSHProperty v b
prop_tuple_list_integer2 = makePropEq id id

prop_tuple_list_integer3 :: (BackendVector b, VectorLang v) => ([Integer], [Integer], [Integer]) -> DSHProperty v b
prop_tuple_list_integer3 = makePropEq id id

prop_tuple_integer_list :: (BackendVector b, VectorLang v) => (Integer, [Integer]) -> DSHProperty v b
prop_tuple_integer_list = makePropEq id id

prop_tuple_integer_list_integer :: (BackendVector b, VectorLang v) => (Integer, [Integer], Integer) -> DSHProperty v b
prop_tuple_integer_list_integer = makePropEq id id

prop_either_integer :: (BackendVector b, VectorLang v) => Either Integer Integer -> DSHProperty v b
prop_either_integer = makePropEq id id

prop_tuple4 :: (BackendVector b, VectorLang v) => [(Integer, Integer, Integer, Integer)] -> DSHProperty v b
prop_tuple4 = makePropEq (Q.map (\(Q.view -> (a, b, c, d)) -> Q.tup4 (a + c) (b - d) b d))
                         (map (\(a, b, c, d) -> (a + c, b - d, b, d)))

prop_tuple5 :: (BackendVector b, VectorLang v) => [(Integer, Integer, Integer, Integer, Integer)] -> DSHProperty v b
prop_tuple5 = makePropEq (Q.map (\(Q.view -> (a, _, c, _, e)) -> Q.tup3 a c e))
                         (map (\(a, _, c, _, e) -> (a, c, e)))

-- {-

-- prop_d0 :: (BackendVector b, VectorLang v) => D0 -> DSHProperty v b
-- prop_d0 = makePropEq id id

-- prop_d1 :: (BackendVector b, VectorLang v) => D1 Integer -> DSHProperty v b
-- prop_d1 = makePropEq id id

-- prop_d2 :: (BackendVector b, VectorLang v) => D2 Integer Integer -> DSHProperty v b
-- prop_d2 = makePropEq id id

-- prop_d3 :: (BackendVector b, VectorLang v) => D3 -> DSHProperty v b
-- prop_d3 = makePropEq id id

-- prop_d4 :: (BackendVector b, VectorLang v) => D4 Integer -> DSHProperty v b
-- prop_d4 = makePropEq id id

-- prop_d5 :: (BackendVector b, VectorLang v) => D5 Integer -> DSHProperty v b
-- prop_d5 = makePropEq id id

-- prop_d6 :: (BackendVector b, VectorLang v) => D6 Integer Integer Integer Integer Integer -> DSHProperty v b
-- prop_d6 = makePropEq id id

-- -}

-- * Equality, Boolean Logic and Ordering

prop_infix_and :: (BackendVector b, VectorLang v) => (Bool,Bool) -> DSHProperty v b
prop_infix_and = makePropEq (uncurryQ (Q.&&)) (uncurry (&&))

prop_infix_map_and :: (BackendVector b, VectorLang v) => (Bool, [Bool]) -> DSHProperty v b
prop_infix_map_and = makePropEq (\x -> Q.map (Q.fst x Q.&&) $ Q.snd x) (\(x,xs) -> map (x &&) xs)

prop_infix_or :: (BackendVector b, VectorLang v) => (Bool,Bool) -> DSHProperty v b
prop_infix_or = makePropEq (uncurryQ (Q.||)) (uncurry (||))

prop_infix_map_or :: (BackendVector b, VectorLang v) => (Bool, [Bool]) -> DSHProperty v b
prop_infix_map_or = makePropEq (\x -> Q.map (Q.fst x Q.||) $ Q.snd x) (\(x,xs) -> map (x ||) xs)

prop_not :: (BackendVector b, VectorLang v) => Bool -> DSHProperty v b
prop_not = makePropEq Q.not not

prop_map_not :: (BackendVector b, VectorLang v) => [Bool] -> DSHProperty v b
prop_map_not = makePropEq (Q.map Q.not) (map not)

prop_eq :: (BackendVector b, VectorLang v) => (Integer,Integer) -> DSHProperty v b
prop_eq = makePropEq (uncurryQ (Q.==)) (uncurry (==))

prop_map_eq :: (BackendVector b, VectorLang v) => (Integer, [Integer]) -> DSHProperty v b
prop_map_eq = makePropEq (\x -> Q.map (Q.fst x Q.==) $ Q.snd x) (\(x,xs) -> map (x ==) xs)

prop_neq :: (BackendVector b, VectorLang v) => (Integer,Integer) -> DSHProperty v b
prop_neq = makePropEq (uncurryQ (Q./=)) (uncurry (/=))

prop_map_neq :: (BackendVector b, VectorLang v) => (Integer, [Integer]) -> DSHProperty v b
prop_map_neq = makePropEq (\x -> Q.map (Q.fst x Q./=) $ Q.snd x) (\(x,xs) -> map (x /=) xs)

prop_cond :: (BackendVector b, VectorLang v) => Bool -> DSHProperty v b
prop_cond = makePropEq (\b -> Q.cond b 0 1) (\b -> if b then (0 :: Integer) else 1)

prop_cond_tuples :: (BackendVector b, VectorLang v) => (Bool, (Integer, Integer)) -> DSHProperty v b
prop_cond_tuples = makePropEq (\b -> Q.cond (Q.fst b)
                                          (Q.pair (Q.fst $ Q.snd b) (Q.fst $ Q.snd b))
                                          (Q.pair (Q.snd $ Q.snd b) (Q.snd $ Q.snd b)))
                            (\b -> if fst b
                                   then (fst $ snd b, fst $ snd b)
                                   else (snd $ snd b, snd $ snd b))

prop_cond_list_tuples :: (BackendVector b, VectorLang v) => (Bool, ([[Integer]], [[Integer]])) -> DSHProperty v b
prop_cond_list_tuples = makePropEq (\b -> Q.cond (Q.fst b)
                                               (Q.pair (Q.fst $ Q.snd b) (Q.fst $ Q.snd b))
                                               (Q.pair (Q.snd $ Q.snd b) (Q.snd $ Q.snd b)))
                                 (\b -> if fst b
                                        then (fst $ snd b, fst $ snd b)
                                        else (snd $ snd b, snd $ snd b))

prop_map_cond :: (BackendVector b, VectorLang v) => [Bool] -> DSHProperty v b
prop_map_cond = makePropEq (Q.map (\b -> Q.cond b (0 :: Q.Q Integer) 1))
                         (map (\b -> if b then 0 else 1))

prop_map_cond_tuples :: (BackendVector b, VectorLang v) => [Bool] -> DSHProperty v b
prop_map_cond_tuples = makePropEq (Q.map (\b -> Q.cond b
                                                     (Q.toQ (0, 10) :: Q.Q (Integer, Integer))
                                                     (Q.toQ (1, 11))))
                                (map (\b -> if b
                                            then (0, 10)
                                            else (1, 11)))

prop_concatmapcond :: (BackendVector b, VectorLang v) => [Integer] -> DSHProperty v b
prop_concatmapcond =
    makePropEq q n
        where q l = Q.concatMap (\x -> Q.cond ((Q.>) x (Q.toQ 0)) (x Q.<| el) el) l
              n l = concatMap (\x -> if x > 0 then [x] else []) l
              el = Q.toQ []

prop_lt :: (BackendVector b, VectorLang v) => (Integer, Integer) -> DSHProperty v b
prop_lt = makePropEq (uncurryQ (Q.<)) (uncurry (<))

prop_map_lt :: (BackendVector b, VectorLang v) => (Integer, [Integer]) -> DSHProperty v b
prop_map_lt = makePropEq (\x -> Q.map (Q.fst x Q.<) $ Q.snd x) (\(x,xs) -> map (x <) xs)

prop_lte :: (BackendVector b, VectorLang v) => (Integer, Integer) -> DSHProperty v b
prop_lte = makePropEq (uncurryQ (Q.<=)) (uncurry (<=))

prop_map_lte :: (BackendVector b, VectorLang v) => (Integer, [Integer]) -> DSHProperty v b
prop_map_lte = makePropEq (\x -> Q.map (Q.fst x Q.<=) $ Q.snd x) (\(x,xs) -> map (x <=) xs)

prop_gt :: (BackendVector b, VectorLang v) => (Integer, Integer) -> DSHProperty v b
prop_gt = makePropEq (uncurryQ (Q.>)) (uncurry (>))

prop_map_gt :: (BackendVector b, VectorLang v) => (Integer, [Integer]) -> DSHProperty v b
prop_map_gt = makePropEq (\x -> Q.map (Q.fst x Q.>) $ Q.snd x) (\(x,xs) -> map (x >) xs)

prop_gte :: (BackendVector b, VectorLang v) => (Integer, Integer) -> DSHProperty v b
prop_gte = makePropEq (uncurryQ (Q.>=)) (uncurry (>=))

prop_map_gte :: (BackendVector b, VectorLang v) => (Integer, [Integer]) -> DSHProperty v b
prop_map_gte = makePropEq (\x -> Q.map (Q.fst x Q.>=) $ Q.snd x) (\(x,xs) -> map (x >=) xs)

prop_min_integer :: (BackendVector b, VectorLang v) => (Integer,Integer) -> DSHProperty v b
prop_min_integer = makePropEq (uncurryQ Q.min) (uncurry min)

prop_max_integer :: (BackendVector b, VectorLang v) => (Integer,Integer) -> DSHProperty v b
prop_max_integer = makePropEq (uncurryQ Q.max) (uncurry max)

prop_min_double :: (BackendVector b, VectorLang v) => (Fixed Double, Fixed Double) -> DSHProperty v b
prop_min_double (d1, d2) = makePropDouble (uncurryQ Q.min) (uncurry min) (getFixed d1, getFixed d2)

prop_max_double :: (BackendVector b, VectorLang v) => (Fixed Double, Fixed Double) -> DSHProperty v b
prop_max_double (d1, d2) = makePropDouble (uncurryQ Q.max) (uncurry max) (getFixed d1, getFixed d2)

-- * Maybe

prop_maybe :: (BackendVector b, VectorLang v) => (Integer, Maybe Integer) -> DSHProperty v b
prop_maybe =  makePropEq (\a -> Q.maybe (Q.fst a) id (Q.snd a)) (\(i,mi) -> maybe i id mi)

prop_just :: (BackendVector b, VectorLang v) => Integer -> DSHProperty v b
prop_just = makePropEq Q.just Just

prop_isJust :: (BackendVector b, VectorLang v) => Maybe Integer -> DSHProperty v b
prop_isJust = makePropEq Q.isJust isJust

prop_isNothing :: (BackendVector b, VectorLang v) => Maybe Integer -> DSHProperty v b
prop_isNothing = makePropEq Q.isNothing isNothing

prop_fromJust :: (BackendVector b, VectorLang v) => Integer -> DSHProperty v b
prop_fromJust i = makePropEq Q.fromJust fromJust (Just i)

prop_fromMaybe :: (BackendVector b, VectorLang v) => (Integer,Maybe Integer) -> DSHProperty v b
prop_fromMaybe = makePropEq (uncurryQ Q.fromMaybe) (uncurry fromMaybe)

prop_listToMaybe :: (BackendVector b, VectorLang v) => [Integer] -> DSHProperty v b
prop_listToMaybe = makePropEq Q.listToMaybe listToMaybe

prop_maybeToList :: (BackendVector b, VectorLang v) => Maybe Integer -> DSHProperty v b
prop_maybeToList = makePropEq Q.maybeToList maybeToList

prop_catMaybes :: (BackendVector b, VectorLang v) => [Maybe Integer] -> DSHProperty v b
prop_catMaybes = makePropEq Q.catMaybes catMaybes

prop_mapMaybe :: (BackendVector b, VectorLang v) => [Maybe Integer] -> DSHProperty v b
prop_mapMaybe = makePropEq (Q.mapMaybe id) (mapMaybe id)

-- * Either

prop_left :: (BackendVector b, VectorLang v) => Integer -> DSHProperty v b
prop_left = makePropEq (Q.left :: Q.Q Integer -> Q.Q (Either Integer Integer)) Left

prop_right :: (BackendVector b, VectorLang v) => Integer -> DSHProperty v b
prop_right = makePropEq (Q.right :: Q.Q Integer -> Q.Q (Either Integer Integer)) Right

prop_isLeft :: (BackendVector b, VectorLang v) => Either Integer Integer -> DSHProperty v b
prop_isLeft = makePropEq Q.isLeft (\e -> case e of {Left _ -> True; Right _ -> False;})

prop_isRight :: (BackendVector b, VectorLang v) => Either Integer Integer -> DSHProperty v b
prop_isRight = makePropEq Q.isRight (\e -> case e of {Left _ -> False; Right _ -> True;})

prop_either :: (BackendVector b, VectorLang v) => Either Integer Integer -> DSHProperty v b
prop_either =  makePropEq (Q.either id id) (either id id)

prop_lefts :: (BackendVector b, VectorLang v) => [Either Integer Integer] -> DSHProperty v b
prop_lefts =  makePropEq Q.lefts lefts

prop_rights :: (BackendVector b, VectorLang v) => [Either Integer Integer] -> DSHProperty v b
prop_rights =  makePropEq Q.rights rights

prop_partitionEithers :: (BackendVector b, VectorLang v) => [Either Integer Integer] -> DSHProperty v b
prop_partitionEithers =  makePropEq Q.partitionEithers partitionEithers

-- * Lists

prop_cons :: (BackendVector b, VectorLang v) => (Integer, [Integer]) -> DSHProperty v b
prop_cons = makePropEq (uncurryQ (Q.<|)) (uncurry (:))

prop_map_cons :: (BackendVector b, VectorLang v) => (Integer, [[Integer]]) -> DSHProperty v b
prop_map_cons = makePropEq (\x -> Q.map (Q.fst x Q.<|) $ Q.snd x)
                         (\(x,xs) -> map (x:) xs)

prop_snoc :: (BackendVector b, VectorLang v) => ([Integer], Integer) -> DSHProperty v b
prop_snoc = makePropEq (uncurryQ (Q.|>)) (\(a,b) -> a ++ [b])

prop_map_snoc :: (BackendVector b, VectorLang v) => ([Integer], [Integer]) -> DSHProperty v b
prop_map_snoc = makePropEq (\z -> Q.map (Q.fst z Q.|>) (Q.snd z)) (\(a,b) -> map (\z -> a ++ [z]) b)

prop_singleton :: (BackendVector b, VectorLang v) => Integer -> DSHProperty v b
prop_singleton = makePropEq Q.singleton (: [])

prop_head :: (BackendVector b, VectorLang v) => NonEmptyList Integer -> DSHProperty v b
prop_head (NonEmpty is) = makePropEq Q.head head is

prop_tail :: (BackendVector b, VectorLang v) => NonEmptyList Integer -> DSHProperty v b
prop_tail (NonEmpty is) = makePropEq Q.tail tail is

prop_last :: (BackendVector b, VectorLang v) => NonEmptyList Integer -> DSHProperty v b
prop_last (NonEmpty is) = makePropEq Q.last last is

prop_map_last :: (BackendVector b, VectorLang v) => [NonEmptyList Integer] -> DSHProperty v b
prop_map_last ps =
    makePropEq (Q.map Q.last) (map last) (map getNonEmpty ps)

prop_init :: (BackendVector b, VectorLang v) => NonEmptyList Integer -> DSHProperty v b
prop_init (NonEmpty is) = makePropEq Q.init init is

prop_map_init  :: (BackendVector b, VectorLang v) => [NonEmptyList Integer] -> DSHProperty v b
prop_map_init ps =
    makePropEq (Q.map Q.init) (map init) (map getNonEmpty ps)

prop_the   :: (BackendVector b, VectorLang v) => (Positive Int, Integer) -> DSHProperty v b
prop_the (n, i) =
    makePropEq Q.head the l
  where
    l = replicate (getPositive n) i

prop_map_the :: (BackendVector b, VectorLang v) => [(Positive Int, Integer)] -> DSHProperty v b
prop_map_the ps =
    makePropEq (Q.map Q.head) (map the) xss
  where
    xss = map (\(Positive n, i) -> replicate n i) ps

prop_map_tail :: (BackendVector b, VectorLang v) => [NonEmptyList Integer] -> DSHProperty v b
prop_map_tail ps =
    makePropEq (Q.map Q.tail) (map tail) (map getNonEmpty ps)

prop_index :: (BackendVector b, VectorLang v) => ([Integer], NonNegative Integer)  -> DSHProperty v b
prop_index (l, NonNegative i) codeGen conn =
    i < fromIntegral (length l)
    ==>
    makePropEq (uncurryQ (Q.!!))
               (\(a,b) -> a !! fromIntegral b)
               (l, i)
               codeGen conn

prop_index_pair :: (BackendVector b, VectorLang v) => ([(Integer, [Integer])], NonNegative Integer) -> DSHProperty v b
prop_index_pair (l, NonNegative i) codeGen conn =
    i < fromIntegral (length l)
    ==>
    makePropEq (uncurryQ (Q.!!))
               (\(a,b) -> a !! fromIntegral b)
               (l, i)
               codeGen conn

prop_index_nest :: (BackendVector b, VectorLang v) => ([[Integer]], NonNegative Integer)  -> DSHProperty v b
prop_index_nest (l, NonNegative i) codeGen conn =
    i < fromIntegral (length l)
    ==>
    makePropEq (uncurryQ (Q.!!))
               (\(a,b) -> a !! fromIntegral b)
               (l, i)
               codeGen conn

prop_map_index2 :: (BackendVector b, VectorLang v) => (NonEmptyList Integer, [NonNegative Integer]) -> DSHProperty v b
prop_map_index2 (nl, is) =
    makePropEq (\z -> Q.map (\i -> Q.fst z Q.!! i) (Q.snd z))
               (\z -> map (\i -> (fst z) !! fromIntegral i) $ snd z)
               (l, is')
  where
    l   = getNonEmpty nl
    is' = map ((`mod` fromIntegral (length l)) . getNonNegative) is

prop_map_index :: (BackendVector b, VectorLang v) => ([Integer], [NonNegative Integer])  -> DSHProperty v b
prop_map_index (l, is) codeGen conn =
    and [i < 3 * fromIntegral (length l) | NonNegative i <-  is]
    ==>
    makePropEq (\z -> Q.map ((Q.fst z Q.++ Q.fst z Q.++ Q.fst z) Q.!!)
                            (Q.snd z))
               (\(a,b) -> map (((a ++ a ++ a) !!) . fromIntegral) b)
               (l, map getNonNegative is)
               codeGen conn

prop_map_index_nest :: (BackendVector b, VectorLang v) => ([[Integer]], [NonNegative Integer])  -> DSHProperty v b
prop_map_index_nest (l, is) codeGen conn =
    and [i < 3 * fromIntegral (length l) | NonNegative i <-  is]
    ==> makePropEq (\z -> Q.map (((Q.fst z) Q.++ (Q.fst z) Q.++ (Q.fst z)) Q.!!)
                                (Q.snd z))
                   (\(a,b) -> map ((a ++ a ++ a) !!) (map fromIntegral b))
                   (l, map getNonNegative is)
                   codeGen conn

prop_take :: (BackendVector b, VectorLang v) => (Integer, [Integer]) -> DSHProperty v b
prop_take = makePropEq (uncurryQ Q.take) (\(n,l) -> take (fromIntegral n) l)

prop_map_take :: (BackendVector b, VectorLang v) => (Integer, [[Integer]]) -> DSHProperty v b
prop_map_take = makePropEq (\z -> Q.map (Q.take $ Q.fst z) $ Q.snd z)
                           (\(n,l) -> map (take (fromIntegral n)) l)

prop_drop :: (BackendVector b, VectorLang v) => (Integer, [Integer]) -> DSHProperty v b
prop_drop = makePropEq (uncurryQ Q.drop) (\(n,l) -> drop (fromIntegral n) l)

prop_map_drop :: (BackendVector b, VectorLang v) => (Integer, [[Integer]]) -> DSHProperty v b
prop_map_drop = makePropEq (\z -> Q.map (Q.drop $ Q.fst z) $ Q.snd z)
                           (\(n,l) -> map (drop (fromIntegral n)) l)

prop_takedrop :: (BackendVector b, VectorLang v) => (Integer, [Integer]) -> DSHProperty v b
prop_takedrop = makePropEq takedrop_q takedrop
  where
    takedrop_q p    = Q.append ((Q.take (Q.fst p)) (Q.snd p))
                               ((Q.drop (Q.fst p)) (Q.snd p))
    takedrop (n, l) = (take (fromIntegral n) l)
                      ++
                      (drop (fromIntegral n) l)

prop_map :: (BackendVector b, VectorLang v) => [Integer] -> DSHProperty v b
prop_map = makePropEq (Q.map id) (map id)

prop_map_map_mul :: (BackendVector b, VectorLang v) => [[Integer]] -> DSHProperty v b
prop_map_map_mul = makePropEq (Q.map (Q.map (*2))) (map (map (*2)))

prop_map_map_add :: (BackendVector b, VectorLang v) => ([Integer], [Integer]) -> DSHProperty v b
prop_map_map_add = makePropEq (\z -> Q.map (\x -> (Q.map (\y -> x + y) $ Q.snd z))
                                           (Q.fst z))
                              (\(l,r) -> map (\x -> map (\y -> x + y) r) l)

prop_map_map_map_mul :: (BackendVector b, VectorLang v) => [[[Integer]]] -> DSHProperty v b
prop_map_map_map_mul = makePropEq (Q.map (Q.map (Q.map (*2)))) (map (map (map (*2))))

prop_append :: (BackendVector b, VectorLang v) => ([Integer], [Integer]) -> DSHProperty v b
prop_append = makePropEq (uncurryQ (Q.++)) (uncurry (++))

prop_append_nest :: (BackendVector b, VectorLang v) => ([[Integer]], [[Integer]]) -> DSHProperty v b
prop_append_nest = makePropEq (uncurryQ (Q.append)) (\(a,b) -> a ++ b)

prop_map_append :: (BackendVector b, VectorLang v) => ([Integer], [[Integer]]) -> DSHProperty v b
prop_map_append = makePropEq (\z -> Q.map (Q.fst z Q.++) (Q.snd z)) (\(a,b) -> map (a ++) b)

prop_filter :: (BackendVector b, VectorLang v) => [Integer] -> DSHProperty v b
prop_filter = makePropEq (Q.filter (const $ Q.toQ True)) (filter $ const True)

prop_filter_gt :: (BackendVector b, VectorLang v) => [Integer] -> DSHProperty v b
prop_filter_gt = makePropEq (Q.filter (Q.> 42)) (filter (> 42))

prop_filter_gt_nested :: (BackendVector b, VectorLang v) => [(Integer, [Integer])] -> DSHProperty v b
prop_filter_gt_nested = makePropEq (Q.filter ((Q.> 42) . Q.fst)) (filter ((> 42) . fst))

prop_map_filter :: (BackendVector b, VectorLang v) => [[Integer]] -> DSHProperty v b
prop_map_filter = makePropEq (Q.map (Q.filter (const $ Q.toQ True))) (map (filter $ const True))

prop_map_filter_gt :: (BackendVector b, VectorLang v) => [[Integer]] -> DSHProperty v b
prop_map_filter_gt = makePropEq (Q.map (Q.filter (Q.> 42))) (map (filter (> 42)))

prop_map_filter_gt_nested :: (BackendVector b, VectorLang v) => [[(Integer, [Integer])]] -> DSHProperty v b
prop_map_filter_gt_nested = makePropEq (Q.map (Q.filter ((Q.> 42) . Q.fst))) (map (filter ((> 42) . fst)))

prop_groupWith :: (BackendVector b, VectorLang v) => [Integer] -> DSHProperty v b
prop_groupWith = makePropEq (Q.groupWith id) (groupWith id)

groupWithKey :: Ord b => (a -> b) -> [a] -> [(b, [a])]
groupWithKey p as = map (\g -> (the $ map p g, g)) $ groupWith p as

prop_groupWithKey :: (BackendVector b, VectorLang v) => [Integer] -> DSHProperty v b
prop_groupWithKey = makePropEq (Q.groupWithKey id) (groupWithKey id)

prop_map_groupWith_rem :: (BackendVector b, VectorLang v) => [[Integer]] -> DSHProperty v b
prop_map_groupWith_rem = makePropEq (Q.map (Q.groupWith (`Q.rem` 10)))
                                    (map (groupWith (`rem` 10)))

prop_map_groupWith :: (BackendVector b, VectorLang v) => [[Integer]] -> DSHProperty v b
prop_map_groupWith = makePropEq (Q.map (Q.groupWith id)) (map (groupWith id))

prop_map_groupWithKey :: (BackendVector b, VectorLang v) => [[Integer]] -> DSHProperty v b
prop_map_groupWithKey = makePropEq (Q.map (Q.groupWithKey id)) (map (groupWithKey id))

prop_groupWith_length :: (BackendVector b, VectorLang v) => [[Integer]] -> DSHProperty v b
prop_groupWith_length = makePropEq (Q.groupWith Q.length) (groupWith length)

prop_groupWithKey_length :: (BackendVector b, VectorLang v) => [[Integer]] -> DSHProperty v b
prop_groupWithKey_length = makePropEq (Q.groupWithKey Q.length) (groupWithKey (fromIntegral . length))

prop_groupagg_sum :: (BackendVector b, VectorLang v) => [Integer] -> DSHProperty v b
prop_groupagg_sum = makePropEq (Q.map Q.sum . Q.groupWith (`Q.rem` 10))
                               (map sum . groupWith (`rem` 10))

prop_groupaggkey_sum :: (BackendVector b, VectorLang v) => [Integer] -> DSHProperty v b
prop_groupaggkey_sum = makePropEq (Q.map (\(Q.view -> (k, g)) -> Q.pair k (Q.sum g)) . Q.groupWithKey (`Q.rem` 10))
                                  (map (\(k, g) -> (k, sum g)) . groupWithKey (`rem` 10))

prop_groupagg_sum_exp :: (BackendVector b, VectorLang v) => [Integer] -> DSHProperty v b
prop_groupagg_sum_exp = makePropEq (Q.map Q.sum . Q.map (Q.map (* 3)) . Q.groupWith (`Q.rem` 10))
                                   (map sum . map (map (* 3)) . groupWith (`rem` 10))

prop_groupagg_length :: (BackendVector b, VectorLang v) => [Integer] -> DSHProperty v b
prop_groupagg_length = makePropEq (Q.map Q.length . Q.groupWith (`Q.rem` 10))
                                  (map (fromIntegral . length) . groupWith (`rem` 10))

prop_groupagg_minimum :: (BackendVector b, VectorLang v) => NonEmptyList Integer -> DSHProperty v b
prop_groupagg_minimum is = makePropEq (Q.map Q.minimum . Q.groupWith (`Q.rem` 10))
                                      (map minimum . groupWith (`rem` 10))
                                      (getNonEmpty is)

prop_groupagg_maximum :: (BackendVector b, VectorLang v) => NonEmptyList Integer -> DSHProperty v b
prop_groupagg_maximum is = makePropEq (Q.map Q.maximum . Q.groupWith (`Q.rem` 10))
                                      (map maximum . groupWith (`rem` 10))
                                      (getNonEmpty is)

prop_groupagg_avg :: (BackendVector b, VectorLang v) => NonEmptyList Double -> DSHProperty v b
prop_groupagg_avg is = makePropDoubles (Q.map Q.avg . Q.groupWith (Q.> 0))
                                       (map avgDouble . groupWith (> 0))
                                       (getNonEmpty is)

prop_groupagg_sum_length :: (BackendVector b, VectorLang v) => [Integer] -> DSHProperty v b
prop_groupagg_sum_length = makePropEq (Q.map (\g -> Q.tup2 (Q.sum g) (Q.length g)) . Q.groupWith (`Q.rem` 10))
                                      (map (\g -> (sum g, fromIntegral $ length g)) . groupWith (`rem` 10))

prop_groupaggkey_sum_length :: (BackendVector b, VectorLang v) => [Integer] -> DSHProperty v b
prop_groupaggkey_sum_length = makePropEq (Q.map (\(Q.view -> (k, g)) -> Q.tup3 k (Q.sum g) (Q.length g)) . Q.groupWithKey (`Q.rem` 10))
                                         (map (\(k, g) -> (k, sum g, fromIntegral $ length g)) . groupWithKey (`rem` 10))

prop_groupagg_sum_length_max :: (BackendVector b, VectorLang v) => [Integer] -> DSHProperty v b
prop_groupagg_sum_length_max = makePropEq (Q.map (\g -> Q.tup3 (Q.sum g) (Q.length g) (Q.maximum g)) . Q.groupWith (`Q.rem` 10))
                                          (map (\g -> (sum g, fromIntegral $ length g, maximum g)) . groupWith (`rem` 10))

prop_sortWith  :: (BackendVector b, VectorLang v) => [Integer] -> DSHProperty v b
prop_sortWith = makePropEq (Q.sortWith id) (sortWith id)

prop_sortWith_pair :: (BackendVector b, VectorLang v) => [(Integer, Integer)] -> DSHProperty v b
prop_sortWith_pair = makePropEq (Q.sortWith Q.fst) (sortWith fst)

-- Test whether we keep the stable sorting semantics of sortWith.
prop_sortWith_pair_stable :: (BackendVector b, VectorLang v) => [(Char, Integer)] -> DSHProperty v b
prop_sortWith_pair_stable = makePropEq (Q.sortWith Q.fst) (sortWith fst)

prop_sortWith_nest  :: (BackendVector b, VectorLang v) => [(Integer, [Integer])] -> DSHProperty v b
prop_sortWith_nest = makePropEq (Q.sortWith Q.fst) (sortWith fst)

prop_map_sortWith :: (BackendVector b, VectorLang v) => [[Integer]] -> DSHProperty v b
prop_map_sortWith = makePropEq (Q.map (Q.sortWith id)) (map (sortWith id))

prop_map_sortWith_pair :: (BackendVector b, VectorLang v) => [[(Integer, Integer)]] -> DSHProperty v b
prop_map_sortWith_pair = makePropEq (Q.map (Q.sortWith Q.fst)) (map (sortWith fst))

prop_map_sortWith_nest :: (BackendVector b, VectorLang v) => [[(Integer, [Integer])]] -> DSHProperty v b
prop_map_sortWith_nest = makePropEq (Q.map (Q.sortWith Q.fst)) (map (sortWith fst))

prop_map_sortWith_length :: (BackendVector b, VectorLang v) => [[[Integer]]] -> DSHProperty v b
prop_map_sortWith_length = makePropEq (Q.map (Q.sortWith Q.length)) (map (sortWith length))

prop_map_groupWith_length :: (BackendVector b, VectorLang v) => [[[Integer]]] -> DSHProperty v b
prop_map_groupWith_length = makePropEq (Q.map (Q.groupWith Q.length)) (map (groupWith length))

prop_map_groupWithKey_length :: (BackendVector b, VectorLang v) => [[[Integer]]] -> DSHProperty v b
prop_map_groupWithKey_length = makePropEq (Q.map (Q.groupWithKey Q.length))
                                          (map (groupWithKey (fromIntegral . length)))

prop_map_groupagg_sum :: (BackendVector b, VectorLang v) => [[Integer]] -> DSHProperty v b
prop_map_groupagg_sum = makePropEq (Q.map (Q.map Q.sum) . Q.map (Q.groupWith (`Q.rem` 10)))
                                   (map (map sum) . map (groupWith (`rem` 10)))

prop_map_groupaggkey_sum :: (BackendVector b, VectorLang v) => [[Integer]] -> DSHProperty v b
prop_map_groupaggkey_sum = makePropEq (Q.map (Q.map (\(Q.view -> (k, g)) -> Q.pair k (Q.sum g))) . Q.map (Q.groupWithKey (`Q.rem` 10)))
                                      (map (map (\(k, g) -> (k, sum g))) . map (groupWithKey (`rem` 10)))

prop_map_groupagg_sum_exp :: (BackendVector b, VectorLang v) => [[Integer]] -> DSHProperty v b
prop_map_groupagg_sum_exp = makePropEq (Q.map (Q.map Q.sum) . Q.map (Q.map (Q.map (* 3))) . Q.map (Q.groupWith (`Q.rem` 10)))
                                       (map (map sum) . map (map (map (* 3))) . map (groupWith (`rem` 10)))

prop_map_groupagg_length :: (BackendVector b, VectorLang v) => [[Integer]] -> DSHProperty v b
prop_map_groupagg_length = makePropEq (Q.map (Q.map Q.length) . Q.map (Q.groupWith (`Q.rem` 10)))
                                      (map (map (fromIntegral . length)) . map (groupWith (`rem` 10)))

prop_map_groupagg_minimum :: (BackendVector b, VectorLang v) => [NonEmptyList Integer] -> DSHProperty v b
prop_map_groupagg_minimum is = makePropEq (Q.map (Q.map Q.minimum) . Q.map (Q.groupWith (`Q.rem` 10)))
                                          (map (map minimum) . map (groupWith (`rem` 10)))
                                          (map getNonEmpty is)

prop_map_groupagg_maximum :: (BackendVector b, VectorLang v) => [NonEmptyList Integer] -> DSHProperty v b
prop_map_groupagg_maximum is = makePropEq (Q.map (Q.map Q.maximum) . Q.map (Q.groupWith (`Q.rem` 10)))
                                          (map (map maximum) . map (groupWith (`rem` 10)))
                                          (map getNonEmpty is)

prop_map_groupagg_sum_length :: (BackendVector b, VectorLang v) => [[Integer]] -> DSHProperty v b
prop_map_groupagg_sum_length = makePropEq (Q.map (Q.map (\g -> Q.tup2 (Q.sum g) (Q.length g))) . Q.map (Q.groupWith (`Q.rem` 10)))
                                          (map (map (\g -> (sum g, fromIntegral $ length g))) . map (groupWith (`rem` 10)))

prop_map_groupaggkey_sum_length :: (BackendVector b, VectorLang v) => [[Integer]] -> DSHProperty v b
prop_map_groupaggkey_sum_length = makePropEq (Q.map (Q.map (\(Q.view -> (k, g)) -> Q.tup3 k (Q.sum g) (Q.length g))) . Q.map (Q.groupWithKey (`Q.rem` 10)))
                                             (map (map (\(k, g) -> (k, sum g, fromIntegral $ length g))) . map (groupWithKey (`rem` 10)))

prop_map_groupagg_sum_length_max :: (BackendVector b, VectorLang v) => [[Integer]] -> DSHProperty v b
prop_map_groupagg_sum_length_max = makePropEq (Q.map (Q.map (\g -> Q.tup3 (Q.sum g) (Q.length g) (Q.maximum g))) . Q.map (Q.groupWith (`Q.rem` 10)))
                                              (map (map (\g -> (sum g, fromIntegral $ length g, maximum g))) . map (groupWith (`rem` 10)))

prop_sortWith_length_nest  :: (BackendVector b, VectorLang v) => [[[Integer]]] -> DSHProperty v b
prop_sortWith_length_nest = makePropEq (Q.sortWith Q.length) (sortWith length)

prop_groupWith_length_nest :: (BackendVector b, VectorLang v) => [[[Integer]]] -> DSHProperty v b
prop_groupWith_length_nest = makePropEq (Q.groupWith Q.length) (groupWith length)

prop_groupWithKey_length_nest :: (BackendVector b, VectorLang v) => [[[Integer]]] -> DSHProperty v b
prop_groupWithKey_length_nest = makePropEq (Q.groupWithKey Q.length)
                                           (groupWithKey (fromIntegral . length))

prop_null :: (BackendVector b, VectorLang v) => [Integer] -> DSHProperty v b
prop_null = makePropEq Q.null null

prop_map_null :: (BackendVector b, VectorLang v) => [[Integer]] -> DSHProperty v b
prop_map_null = makePropEq (Q.map Q.null) (map null)

prop_length :: (BackendVector b, VectorLang v) => [Integer] -> DSHProperty v b
prop_length = makePropEq Q.length ((fromIntegral :: Int -> Integer) . length)

prop_length_tuple :: (BackendVector b, VectorLang v) => [(Integer, Integer)] -> DSHProperty v b
prop_length_tuple = makePropEq Q.length (fromIntegral . length)

prop_map_length :: (BackendVector b, VectorLang v) => [[Integer]] -> DSHProperty v b
prop_map_length = makePropEq (Q.map Q.length) (map (fromIntegral . length))

prop_map_minimum :: (BackendVector b, VectorLang v) => [NonEmptyList Integer] -> DSHProperty v b
prop_map_minimum ps conn =
    makePropEq (Q.map Q.minimum)
               (map (fromIntegral . minimum))
               (map getNonEmpty ps)
               conn

prop_map_maximum :: (BackendVector b, VectorLang v) => [NonEmptyList Integer] -> DSHProperty v b
prop_map_maximum ps conn =
    makePropEq (Q.map Q.maximum)
               (map (fromIntegral . maximum))
               (map getNonEmpty ps)
               conn

prop_map_map_minimum :: (BackendVector b, VectorLang v) => [[NonEmptyList Integer]] -> DSHProperty v b
prop_map_map_minimum ps conn =
    makePropEq (Q.map (Q.map Q.minimum))
               (map (map(fromIntegral . minimum)))
               (map (map getNonEmpty) ps)
               conn

prop_map_map_maximum :: (BackendVector b, VectorLang v) => [[NonEmptyList Integer]] -> DSHProperty v b
prop_map_map_maximum ps conn =
    makePropEq (Q.map (Q.map Q.maximum))
               (map (map(fromIntegral . maximum)))
               (map (map getNonEmpty) ps)
               conn


prop_map_length_tuple :: (BackendVector b, VectorLang v) => [[(Integer, Integer)]] -> DSHProperty v b
prop_map_length_tuple = makePropEq (Q.map Q.length) (map (fromIntegral . length))

prop_reverse :: (BackendVector b, VectorLang v) => [Integer] -> DSHProperty v b
prop_reverse = makePropEq Q.reverse reverse

prop_reverse_nest :: (BackendVector b, VectorLang v) => [[Integer]] -> DSHProperty v b
prop_reverse_nest = makePropEq Q.reverse reverse

prop_map_reverse :: (BackendVector b, VectorLang v) => [[Integer]] -> DSHProperty v b
prop_map_reverse = makePropEq (Q.map Q.reverse) (map reverse)

prop_map_reverse_nest :: (BackendVector b, VectorLang v) => [[[Integer]]] -> DSHProperty v b
prop_map_reverse_nest = makePropEq (Q.map Q.reverse) (map reverse)

prop_and :: (BackendVector b, VectorLang v) => [Bool] -> DSHProperty v b
prop_and = makePropEq Q.and and

prop_map_and :: (BackendVector b, VectorLang v) => [[Bool]] -> DSHProperty v b
prop_map_and = makePropEq (Q.map Q.and) (map and)

prop_map_map_and :: (BackendVector b, VectorLang v) => [[[Bool]]] -> DSHProperty v b
prop_map_map_and = makePropEq (Q.map (Q.map Q.and)) (map (map and))

prop_or :: (BackendVector b, VectorLang v) => [Bool] -> DSHProperty v b
prop_or = makePropEq Q.or or

prop_map_or :: (BackendVector b, VectorLang v) => [[Bool]] -> DSHProperty v b
prop_map_or = makePropEq (Q.map Q.or) (map or)

prop_map_map_or :: (BackendVector b, VectorLang v) => [[[Bool]]] -> DSHProperty v b
prop_map_map_or = makePropEq (Q.map (Q.map Q.or)) (map (map or))

prop_any_zero :: (BackendVector b, VectorLang v) => [Integer] -> DSHProperty v b
prop_any_zero = makePropEq (Q.any (Q.== 0)) (any (== 0))

prop_map_any_zero :: (BackendVector b, VectorLang v) => [[Integer]] -> DSHProperty v b
prop_map_any_zero = makePropEq (Q.map (Q.any (Q.== 0))) (map (any (== 0)))

prop_all_zero :: (BackendVector b, VectorLang v) => [Integer] -> DSHProperty v b
prop_all_zero = makePropEq (Q.all (Q.== 0)) (all (== 0))

prop_map_all_zero :: (BackendVector b, VectorLang v) => [[Integer]] -> DSHProperty v b
prop_map_all_zero = makePropEq (Q.map (Q.all (Q.== 0))) (map (all (== 0)))

prop_sum_integer :: (BackendVector b, VectorLang v) => [Integer] -> DSHProperty v b
prop_sum_integer = makePropEq Q.sum sum

prop_map_sum :: (BackendVector b, VectorLang v) => [[Integer]] -> DSHProperty v b
prop_map_sum = makePropEq (Q.map Q.sum) (map sum)

prop_map_avg :: (BackendVector b, VectorLang v) => [NonEmptyList (Fixed Double)] -> DSHProperty v b
prop_map_avg is =
    makePropDoubles (Q.map Q.avg) (map avgDouble) (map (map getFixed . getNonEmpty) is)

prop_map_map_sum :: (BackendVector b, VectorLang v) => [[[Integer]]] -> DSHProperty v b
prop_map_map_sum = makePropEq (Q.map (Q.map Q.sum)) (map (map sum))

-- prop_map_map_avg :: (BackendVector b, VectorLang v) => [[NonEmptyList Integer]] -> DSHProperty v b
-- prop_map_map_avg is conn =
--     makePropEq (Q.map (Q.map Q.avg))
--                (map (map avgInt))
--                (map (map getNonEmpty) is)
--                conn

prop_sum_double :: (BackendVector b, VectorLang v) => [Fixed Double] -> DSHProperty v b
prop_sum_double d = makePropDouble Q.sum sum (map getFixed d)

avgDouble :: [Double] -> Double
avgDouble ds = sum ds / (fromIntegral $ length ds)

prop_avg_double :: (BackendVector b, VectorLang v) => NonEmptyList (Fixed Double) -> DSHProperty v b
prop_avg_double ds conn = makePropDouble Q.avg avgDouble (map getFixed $ getNonEmpty ds) conn

prop_concat :: (BackendVector b, VectorLang v) => [[Integer]] -> DSHProperty v b
prop_concat = makePropEq Q.concat concat

prop_map_concat :: (BackendVector b, VectorLang v) => [[[Integer]]] -> DSHProperty v b
prop_map_concat = makePropEq (Q.map Q.concat) (map concat)

prop_concatMap :: (BackendVector b, VectorLang v) => [Integer] -> DSHProperty v b
prop_concatMap = makePropEq (Q.concatMap Q.singleton) (concatMap (: []))

prop_maximum :: (BackendVector b, VectorLang v) => NonEmptyList Integer -> DSHProperty v b
prop_maximum (NonEmpty is) = makePropEq Q.maximum maximum is

prop_minimum :: (BackendVector b, VectorLang v) => NonEmptyList Integer -> DSHProperty v b
prop_minimum (NonEmpty is) = makePropEq Q.minimum minimum is

prop_splitAt :: (BackendVector b, VectorLang v) => (Integer, [Integer]) -> DSHProperty v b
prop_splitAt = makePropEq (uncurryQ Q.splitAt) (\(a,b) -> splitAt (fromIntegral a) b)

prop_takeWhile :: (BackendVector b, VectorLang v) => (Integer, [Integer]) -> DSHProperty v b
prop_takeWhile = makePropEq (uncurryQ $ Q.takeWhile . (Q.==))
                          (uncurry  $   takeWhile . (==))

prop_dropWhile :: (BackendVector b, VectorLang v) => (Integer, [Integer]) -> DSHProperty v b
prop_dropWhile = makePropEq (uncurryQ $ Q.dropWhile . (Q.==))
                          (uncurry  $   dropWhile . (==))

prop_map_takeWhile :: (BackendVector b, VectorLang v) => (Integer, [[Integer]]) -> DSHProperty v b
prop_map_takeWhile = makePropEq (\z -> Q.map (Q.takeWhile (Q.fst z Q.==)) (Q.snd z))
                              (\z -> map (takeWhile (fst z ==)) (snd z))

prop_map_dropWhile :: (BackendVector b, VectorLang v) => (Integer, [[Integer]]) -> DSHProperty v b
prop_map_dropWhile = makePropEq (\z -> Q.map (Q.dropWhile (Q.fst z Q.==)) (Q.snd z))
                              (\z -> map (dropWhile (fst z ==)) (snd z))

prop_span :: (BackendVector b, VectorLang v) => (Integer, [Integer]) -> DSHProperty v b
prop_span = makePropEq (uncurryQ $ Q.span . (Q.==))
                     (uncurry   $   span . (==) . fromIntegral)

prop_map_span :: (BackendVector b, VectorLang v) => (Integer, [[Integer]]) -> DSHProperty v b
prop_map_span = makePropEq (\z -> Q.map (Q.span ((Q.fst z) Q.==)) (Q.snd z))
                         (\z -> map (span (fst z ==)) (snd z))

prop_break :: (BackendVector b, VectorLang v) => (Integer, [Integer]) -> DSHProperty v b
prop_break = makePropEq (uncurryQ $ Q.break . (Q.==))
                      (uncurry   $   break . (==) . fromIntegral)

prop_map_break :: (BackendVector b, VectorLang v) => (Integer, [[Integer]]) -> DSHProperty v b
prop_map_break = makePropEq (\z -> Q.map (Q.break ((Q.fst z) Q.==)) (Q.snd z))
                          (\z -> map (break (fst z ==)) (snd z))

prop_elem :: (BackendVector b, VectorLang v) => (Integer, [Integer]) -> DSHProperty v b
prop_elem = makePropEq (uncurryQ Q.elem)
                     (uncurry    elem)

prop_notElem :: (BackendVector b, VectorLang v) => (Integer, [Integer]) -> DSHProperty v b
prop_notElem = makePropEq (uncurryQ Q.notElem)
                        (uncurry    notElem)

prop_lookup :: (BackendVector b, VectorLang v) => (Integer, [(Integer,Integer)]) -> DSHProperty v b
prop_lookup = makePropEq (uncurryQ Q.lookup)
                       (uncurry    lookup)

prop_zip :: (BackendVector b, VectorLang v) => ([Integer], [Integer]) -> DSHProperty v b
prop_zip = makePropEq (uncurryQ Q.zip) (uncurry zip)

prop_zip_nested :: (BackendVector b, VectorLang v) => ([Integer], [(Integer, [Integer])]) -> DSHProperty v b
prop_zip_nested = makePropEq (uncurryQ Q.zip) (uncurry zip)

prop_zip_tuple1 :: (BackendVector b, VectorLang v) => ([Integer], [(Text, Integer)]) -> DSHProperty v b
prop_zip_tuple1 (xs, tds) =
    makePropEq (uncurryQ Q.zip) (uncurry zip) (xs, tds')
  where
    tds' = map (\(t, d) -> (filterNullChar t, d)) tds

prop_zip_tuple2 :: (BackendVector b, VectorLang v)
                => ([(Integer, Integer)], [(Text, Integer)])
                -> DSHProperty v b
prop_zip_tuple2 (xs, tds) =
    makePropEq (uncurryQ Q.zip) (uncurry zip) (xs, tds')
  where
    tds' = map (\(t, d) -> (filterNullChar t, d)) tds

prop_map_zip :: (BackendVector b, VectorLang v) => ([Integer], [[Integer]]) -> DSHProperty v b
prop_map_zip = makePropEq (\z -> Q.map (Q.zip $ Q.fst z) $ Q.snd z) (\(x, y) -> map (zip x) y)

prop_zipWith :: (BackendVector b, VectorLang v) => ([Integer], [Integer]) -> DSHProperty v b
prop_zipWith = makePropEq (uncurryQ $ Q.zipWith (+)) (uncurry $ zipWith (+))

prop_unzip :: (BackendVector b, VectorLang v) => [(Integer, Integer)] -> DSHProperty v b
prop_unzip = makePropEq Q.unzip unzip

prop_map_unzip :: (BackendVector b, VectorLang v) => [[(Integer, Integer)]] -> DSHProperty v b
prop_map_unzip = makePropEq (Q.map Q.unzip) (map unzip)

prop_zip3 :: (BackendVector b, VectorLang v) => ([Integer], [Integer],[Integer]) -> DSHProperty v b
prop_zip3 = makePropEq (\q -> (case Q.view q of (as,bs,cs) -> Q.zip3 as bs cs))
                     (\(as,bs,cs) -> zip3 as bs cs)

prop_zipWith3 :: (BackendVector b, VectorLang v) => ([Integer], [Integer],[Integer]) -> DSHProperty v b
prop_zipWith3 = makePropEq (\q -> (case Q.view q of (as,bs,cs) -> Q.zipWith3 (\a b c -> a + b + c) as bs cs))
                         (\(as,bs,cs) -> zipWith3 (\a b c -> a + b + c) as bs cs)

prop_unzip3 :: (BackendVector b, VectorLang v) => [(Integer, Integer, Integer)] -> DSHProperty v b
prop_unzip3 = makePropEq Q.unzip3 unzip3

prop_nub :: (BackendVector b, VectorLang v) => [Integer] -> DSHProperty v b
prop_nub = makePropEq Q.nub nub

prop_map_nub :: (BackendVector b, VectorLang v) => [[(Integer, Integer)]] -> DSHProperty v b
prop_map_nub = makePropEq (Q.map Q.nub) (map nub)

-- * Tuples

prop_fst :: (BackendVector b, VectorLang v) => (Integer, Integer) -> DSHProperty v b
prop_fst = makePropEq Q.fst fst

prop_fst_nested :: (BackendVector b, VectorLang v) => ([Integer], [Integer]) -> DSHProperty v b
prop_fst_nested = makePropEq Q.fst fst

prop_map_fst :: (BackendVector b, VectorLang v) => [(Integer, Integer)] -> DSHProperty v b
prop_map_fst = makePropEq (Q.map Q.fst) (map fst)

prop_snd :: (BackendVector b, VectorLang v) => (Integer, Integer) -> DSHProperty v b
prop_snd = makePropEq Q.snd snd

prop_map_snd :: (BackendVector b, VectorLang v) => [(Integer, Integer)] -> DSHProperty v b
prop_map_snd = makePropEq (Q.map Q.snd) (map snd)

prop_snd_nested :: (BackendVector b, VectorLang v) => ([Integer], [Integer]) -> DSHProperty v b
prop_snd_nested = makePropEq Q.snd snd

prop_tup3_1 :: (BackendVector b, VectorLang v) => (Integer, Integer, Integer) -> DSHProperty v b
prop_tup3_1 = makePropEq (\q -> case Q.view q of (a, _, _) -> a) (\(a, _, _) -> a)

prop_tup3_2 :: (BackendVector b, VectorLang v) => (Integer, Integer, Integer) -> DSHProperty v b
prop_tup3_2 = makePropEq (\q -> case Q.view q of (_, b, _) -> b) (\(_, b, _) -> b)

prop_tup3_3 :: (BackendVector b, VectorLang v) => (Integer, Integer, Integer) -> DSHProperty v b
prop_tup3_3 = makePropEq (\q -> case Q.view q of (_, _, c) -> c) (\(_, _, c) -> c)

prop_tup4_2 :: (BackendVector b, VectorLang v) => (Integer, Integer, Integer, Integer) -> DSHProperty v b
prop_tup4_2 = makePropEq (\q -> case Q.view q of (_, b, _, _) -> b) (\(_, b, _, _) -> b)

prop_tup4_4 :: (BackendVector b, VectorLang v) => (Integer, Integer, Integer, Integer) -> DSHProperty v b
prop_tup4_4 = makePropEq (\q -> case Q.view q of (_, _, _, d) -> d) (\(_, _, _, d) -> d)

prop_tup3_nested :: (BackendVector b, VectorLang v) => (Integer, [Integer], Integer) -> DSHProperty v b
prop_tup3_nested = makePropEq (\q -> case Q.view q of (_, b, _) -> b) (\(_, b, _) -> b)

prop_tup4_tup3 :: (BackendVector b, VectorLang v) => (Integer, Integer, Integer, Integer) -> DSHProperty v b
prop_tup4_tup3 = makePropEq (\q -> case Q.view q of (a, b, _, d) -> Q.tup3 a b d)
                          (\(a, b, _, d) -> (a, b, d))

prop_agg_tuple :: (BackendVector b, VectorLang v) => NonEmptyList Integer -> DSHProperty v b
prop_agg_tuple nxs = makePropEq (\is -> Q.tup3 (Q.sum is) (Q.maximum is) (Q.minimum is))
                                (\is -> (sum is, maximum is, minimum is))
                                xs
  where
    xs = getNonEmpty nxs

-- * Numerics

prop_add_integer :: (BackendVector b, VectorLang v) => (Integer,Integer) -> DSHProperty v b
prop_add_integer = makePropEq (uncurryQ (+)) (uncurry (+))

prop_add_integer_sums :: (BackendVector b, VectorLang v) => ([Integer], [Integer]) -> DSHProperty v b
prop_add_integer_sums = makePropEq (\p -> Q.sum (Q.fst p) + Q.sum (Q.snd p))
                                   (\p -> sum (fst p) + sum (snd p))

prop_add_double :: (BackendVector b, VectorLang v) => (Fixed Double, Fixed Double) -> DSHProperty v b
prop_add_double (d1, d2) = makePropDouble (uncurryQ (+)) (uncurry (+)) (getFixed d1, getFixed d2)

prop_mul_integer :: (BackendVector b, VectorLang v) => (Integer,Integer) -> DSHProperty v b
prop_mul_integer = makePropEq (uncurryQ (*)) (uncurry (*))

prop_mul_double :: (BackendVector b, VectorLang v) => (Fixed Double, Fixed Double) -> DSHProperty v b
prop_mul_double (d1, d2) = makePropDouble (uncurryQ (*)) (uncurry (*)) (getFixed d1, getFixed d2)

prop_div_double :: (BackendVector b, VectorLang v) => (Fixed Double, Fixed (NonZero Double)) -> DSHProperty v b
prop_div_double (Fixed x, Fixed (NonZero y)) =
    makePropDouble (uncurryQ (/)) (uncurry (/)) (x,y)

prop_integer_to_double :: (BackendVector b, VectorLang v) => Integer -> DSHProperty v b
prop_integer_to_double = makePropDouble Q.integerToDouble fromInteger

prop_integer_to_double_arith :: (BackendVector b, VectorLang v) => (Integer, Fixed Double) -> DSHProperty v b
prop_integer_to_double_arith (i, d) = makePropDouble (\x -> (Q.integerToDouble (Q.fst x)) + (Q.snd x))
                                                     (\(ni, nd) -> fromInteger ni + nd)
                                                     (i, getFixed d)

prop_map_integer_to_double :: (BackendVector b, VectorLang v) => [Integer] -> DSHProperty v b
prop_map_integer_to_double = makePropDoubles (Q.map Q.integerToDouble) (map fromInteger)

prop_abs_integer :: (BackendVector b, VectorLang v) => Integer -> DSHProperty v b
prop_abs_integer = makePropEq Q.abs abs

prop_abs_double :: (BackendVector b, VectorLang v) => Fixed Double -> DSHProperty v b
prop_abs_double d = makePropDouble Q.abs abs (getFixed d)

prop_signum_integer :: (BackendVector b, VectorLang v) => Integer -> DSHProperty v b
prop_signum_integer = makePropEq Q.signum signum

prop_signum_double :: (BackendVector b, VectorLang v) => Fixed Double -> DSHProperty v b
prop_signum_double d = makePropDouble Q.signum signum (getFixed d)

prop_negate_integer :: (BackendVector b, VectorLang v) => Integer -> DSHProperty v b
prop_negate_integer = makePropEq Q.negate negate

prop_negate_double :: (BackendVector b, VectorLang v) => Fixed Double -> DSHProperty v b
prop_negate_double d = makePropDouble Q.negate negate (getFixed d)

prop_trig_sin :: (BackendVector b, VectorLang v) => Fixed Double -> DSHProperty v b
prop_trig_sin d = makePropDouble Q.sin sin (getFixed d)

prop_trig_cos :: (BackendVector b, VectorLang v) => Fixed Double -> DSHProperty v b
prop_trig_cos d = makePropDouble Q.cos cos (getFixed d)

prop_trig_tan :: (BackendVector b, VectorLang v) => Fixed Double -> DSHProperty v b
prop_trig_tan d = makePropDouble Q.tan tan (getFixed d)

prop_exp :: (BackendVector b, VectorLang v) => Fixed Double -> DSHProperty v b
prop_exp d codeGen conn = d >= (-5) && d <= 5 ==> makePropDouble Q.exp exp (getFixed d) codeGen conn

prop_rem :: (BackendVector b, VectorLang v) => Fixed Integer -> DSHProperty v b
prop_rem d = makePropEq (`Q.rem` 10) (`rem` 10) (getFixed d)

prop_log :: (BackendVector b, VectorLang v) => Fixed (Positive Double) -> DSHProperty v b
prop_log d = makePropDouble Q.log log (getPositive $ getFixed d)

prop_sqrt :: (BackendVector b, VectorLang v) => Fixed (Positive Double) -> DSHProperty v b
prop_sqrt d = makePropDouble Q.sqrt sqrt (getPositive $ getFixed d)

arc :: (Ord a, Num a) => a -> Bool
arc d = d >= -1 && d <= 1

prop_trig_asin :: (BackendVector b, VectorLang v) => Fixed Double -> DSHProperty v b
prop_trig_asin d codeGen conn = arc d ==>  makePropDouble Q.asin asin (getFixed d) codeGen conn

prop_trig_acos :: (BackendVector b, VectorLang v) => Fixed Double -> DSHProperty v b
prop_trig_acos d codeGen conn = arc d ==> makePropDouble Q.acos acos (getFixed d) codeGen conn

prop_trig_atan :: (BackendVector b, VectorLang v) => Fixed Double -> DSHProperty v b
prop_trig_atan d = makePropDouble Q.atan atan (getFixed d)

prop_number :: (BackendVector b, VectorLang v) => [Integer] -> DSHProperty v b
prop_number = makePropEq (Q.map Q.snd . Q.number) (\xs -> map snd $ zip xs [1..])

prop_map_number :: (BackendVector b, VectorLang v) => [[Integer]] -> DSHProperty v b
prop_map_number = makePropEq (Q.map (Q.map Q.snd . Q.number))
                            (map (\xs -> map snd $ zip xs [1..]))


prop_map_trig_sin :: (BackendVector b, VectorLang v) => [Fixed Double] -> DSHProperty v b
prop_map_trig_sin ds = makePropDoubles (Q.map Q.sin) (map sin) (map getFixed ds)

prop_map_trig_cos :: (BackendVector b, VectorLang v) => [Fixed Double] -> DSHProperty v b
prop_map_trig_cos ds = makePropDoubles (Q.map Q.cos) (map cos) (map getFixed ds)

prop_map_trig_tan :: (BackendVector b, VectorLang v) => [Fixed Double] -> DSHProperty v b
prop_map_trig_tan ds = makePropDoubles (Q.map Q.tan) (map tan) (map getFixed ds)

prop_map_trig_asin :: (BackendVector b, VectorLang v) => [Fixed Double] -> DSHProperty v b
prop_map_trig_asin ds codeGen conn =
    all arc ds
    ==>
    makePropDoubles (Q.map Q.asin) (map asin) (map getFixed ds) codeGen conn

prop_map_trig_acos :: (BackendVector b, VectorLang v) => [Fixed Double] -> DSHProperty v b
prop_map_trig_acos ds codeGen conn =
    all arc ds
    ==>
    makePropDoubles (Q.map Q.acos) (map acos) (map getFixed ds) codeGen conn

prop_map_trig_atan :: (BackendVector b, VectorLang v) => [Fixed Double] -> DSHProperty v b
prop_map_trig_atan ds = makePropDoubles (Q.map Q.atan) (map atan) (map getFixed ds)

prop_map_exp :: (BackendVector b, VectorLang v) => [Fixed Double] -> DSHProperty v b
prop_map_exp ds codeGen conn =
    all (\d -> d >= (-5) && d <= 5) ds
    ==>
    makePropDoubles (Q.map Q.exp) (map exp) (map getFixed ds) codeGen conn

prop_map_rem :: (BackendVector b, VectorLang v) => [Fixed Integer] -> DSHProperty v b
prop_map_rem d = makePropEq (Q.map (`Q.rem` 10)) (map (`rem` 10)) (map getFixed d)

prop_map_log :: (BackendVector b, VectorLang v) => [Fixed (Positive Double)] -> DSHProperty v b
prop_map_log ds = makePropDoubles (Q.map Q.log) (map log) (map (getPositive . getFixed) ds)

prop_map_sqrt :: (BackendVector b, VectorLang v) => [Fixed (Positive Double)] -> DSHProperty v b
prop_map_sqrt ds =
    makePropDoubles (Q.map Q.sqrt) (map sqrt) (map (getPositive . getFixed) ds)

prop_dist_scalar :: (BackendVector b, VectorLang v) => ([Integer], [Integer]) -> DSHProperty v b
prop_dist_scalar = makePropEq (\p -> Q.map (\i -> Q.sum (Q.fst p) + i) (Q.snd p))
                              (\p -> map (\i -> sum (fst p) + i) (snd p))

prop_dist_list1 :: (BackendVector b, VectorLang v) => ([Integer], [[Integer]]) -> DSHProperty v b
prop_dist_list1 = makePropEq (\p -> Q.map (\xs -> (Q.fst p) Q.++ xs) (Q.snd p))
                             (\p -> map (\xs -> (fst p) ++ xs) (snd p))

prop_dist_list2 :: (BackendVector b, VectorLang v) => ([Integer], [Integer]) -> DSHProperty v b
prop_dist_list2 = makePropEq (\p -> Q.map (\i -> Q.take i (Q.fst p)) (Q.snd p))
                             (\p -> map (\i -> take (fromIntegral i) (fst p)) (snd p))

-- Testcase for lifted disting. This is a first-order version of the running
-- example in Lippmeier et al's paper "Work-Efficient Higher Order
-- Vectorisation" (ICFP 2012).
test_dist_lift :: (BackendVector b, VectorLang v) => DSHAssertion v b
test_dist_lift = makeEqAssertion "dist lift"
                                 (Q.zipWith (\xs is -> Q.map (\i -> xs Q.!! i) is) (Q.toQ xss) (Q.toQ iss))
                                 (zipWith (\xs is -> map (\i -> xs !! fromIntegral i) is) xss iss)
  where
    xss = [['a', 'b'], ['c', 'd', 'e'], ['f', 'g'], ['h']]
    iss = [[1,0,1], [2], [1,0], [0]] :: [[Integer]]

hnegative_sum :: (BackendVector b, VectorLang v) => DSHAssertion v b
hnegative_sum = makeEqAssertion "hnegative_sum" (Q.sum (Q.toQ xs)) (sum xs)
  where
    xs :: [Integer]
    xs = [-1, -4, -5, 2]

hnegative_map_sum :: (BackendVector b, VectorLang v) => DSHAssertion v b
hnegative_map_sum = makeEqAssertion "hnegative_map_sum"
                                    (Q.map Q.sum (Q.toQ xss))
                                    (map sum xss)
  where
    xss :: [[Integer]]
    xss = [[10, 20, 30], [-10, -20, -30], [], [0]]

prop_nub_length :: (BackendVector b, VectorLang v) => [Integer] -> DSHProperty v b
prop_nub_length = makePropEq (Q.length . Q.nub) (fromIntegral . length . nub)

prop_map_nub_length :: (BackendVector b, VectorLang v) => [[Integer]] -> DSHProperty v b
prop_map_nub_length = makePropEq (Q.map (Q.length . Q.nub)) (map (fromIntegral . length . nub))

prop_elem_sort :: (BackendVector b, VectorLang v) => ([Integer], [(Integer, Char)]) -> DSHProperty v b
prop_elem_sort = makePropEq (\(Q.view -> (xs, ys)) -> Q.map (\x -> Q.fst x `Q.elem` xs) $ Q.sortWith Q.snd ys)
                            (\(xs, ys) -> map (\x -> fst x `elem` xs) $ sortWith snd ys)

prop_elem_sort2 :: (BackendVector b, VectorLang v) => ([Integer], [(Integer, Char)]) -> DSHProperty v b
prop_elem_sort2 = makePropEq (\(Q.view -> (xs, ys)) -> Q.filter (\x -> Q.fst x `Q.elem` xs) $ Q.sortWith Q.snd ys)
                             (\(xs, ys) -> filter (\x -> fst x `elem` xs) $ sortWith snd ys)

