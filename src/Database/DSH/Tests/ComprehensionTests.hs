{-# LANGUAGE ViewPatterns #-}

-- | Tests on certain aspects of comprehension nesting.
module Database.DSH.Tests.ComprehensionTests
    ( tests_comprehensions
    , tests_lifted_joins
    , tests_join_hunit
    , tests_nest_head_hunit
    , tests_nest_guard_hunit
    ) where

import           Data.List
import           GHC.Exts

import           Test.HUnit                           (Assertion)
import           Test.QuickCheck
import           Test.Tasty
import qualified Test.Tasty.HUnit                     as TH
import           Test.Tasty.QuickCheck

import qualified Database.DSH                         as Q
import           Database.DSH.Backend
import           Database.DSH.Compiler
import           Database.DSH.Tests.Common
import qualified Database.DSH.Tests.DSHComprehensions as C

{-# ANN module "HLint: ignore Use camelCase" #-}
{-# ANN module "HLint: ignore Avoid lambda" #-}

tests_comprehensions :: (BackendVector b, VectorLang v) => DSHTestTree v b
tests_comprehensions codeGen conn = testGroup "Comprehensions"
    [ testProperty "cartprod" (\a -> prop_cartprod a codeGen conn)
    , testProperty "eqjoin" (\a -> prop_eqjoin a codeGen conn)
    , testProperty "eqjoinproj" (\a -> prop_eqjoinproj a codeGen conn)
    , testProperty "eqjoinpred" (\a -> prop_eqjoinpred a codeGen conn)
    , testProperty "eqjointuples" (\a -> prop_eqjointuples a codeGen conn)
    , testProperty "thetajoin_eq" (\a -> prop_thetajoin_eq a codeGen conn)
    , testProperty "thetajoin_neq" (\a -> prop_thetajoin_neq a codeGen conn)
    , testProperty "eqjoin3" (\a -> prop_eqjoin3 a codeGen conn)
    , testProperty "eqjoin_nested_left" (\a -> prop_eqjoin_nested_left a codeGen conn)
    , testProperty "eqjoin_nested_right" (\a -> prop_eqjoin_nested_right a codeGen conn)
    , testProperty "eqjoin_nested_both" (\a -> prop_eqjoin_nested_both a codeGen conn)
    , testProperty "nestjoin" (\a -> prop_nestjoin a codeGen conn)
    , testProperty "nestjoin3" (\a -> prop_nestjoin3 a codeGen conn)
    , testProperty "groupjoin_length" (\a -> prop_groupjoin_length a codeGen conn)
    , testProperty "groupjoin_length_nub" (\a -> prop_groupjoin_length_nub a codeGen conn)
    , testProperty "groupjoin_sum" (\a -> prop_groupjoin_sum a codeGen conn)
    , testProperty "groupjoin_sum2" (\a -> prop_groupjoin_sum2 a codeGen conn)
    , testProperty "groupjoin_sum_length" (\a -> prop_groupjoin_sum_length a codeGen conn)
    , testProperty "groupjoin_sum_deep" (\a -> prop_groupjoin_sum_deep a codeGen conn)
    , testProperty "groupjoin_length_deep_sum" (\a -> prop_groupjoin_length_deep_sum a codeGen conn)
    , testProperty "groupjoin_sum_length2" (\a -> prop_groupjoin_sum_length2 a codeGen conn)
    , testProperty "groupjoin_length_guard" (\a -> prop_groupjoin_length_guard a codeGen conn)
    , testProperty "groupjoin_length_guard2" (\a -> prop_groupjoin_length_guard2 a codeGen conn)
    , testProperty "groupjoin_sum_nest" (\a -> prop_groupjoin_sum_nest a codeGen conn)
    , testProperty "groupjoin_sum_nest2" (\a -> prop_groupjoin_sum_nest2 a codeGen conn)
    , testProperty "groupjoin_nestjoin" (\a -> prop_groupjoin_nestjoin a codeGen conn)
    , testProperty "groupjoin_nestjoin_guard" (\a -> prop_groupjoin_nestjoin_guard a codeGen conn)
    , testProperty "antijoin class12" (\a -> prop_aj_class12 a codeGen conn)
    , testProperty "antijoin class15" (\a -> prop_aj_class15 a codeGen conn)
    , testProperty "antijoin class16" (\a -> prop_aj_class16 a codeGen conn)
    , testProperty "backdep1" (\a -> prop_backdep a codeGen conn)
    , testProperty "backdep_filter" (\a -> prop_backdep_filter a codeGen conn)
    , testProperty "backdep2" (\a -> prop_backdep2 a codeGen conn)
    , testProperty "backdep3" (\a -> prop_backdep3 a codeGen conn)
    , testProperty "backdep4" (\a -> prop_backdep4 a codeGen conn)
    , testProperty "backdep5" (\a -> prop_backdep5 a codeGen conn)
    , testProperty "deep" (\a -> prop_deep_iter a codeGen conn)
    , testProperty "only tuple" (\a -> prop_only_tuple a codeGen conn)
    , testProperty "njg6" (\a -> prop_njg6 a codeGen conn)
    , testProperty "njg7" (\a -> prop_njg7 a codeGen conn)
    ]

tests_lifted_joins :: (BackendVector b, VectorLang v) => DSHTestTree v b
tests_lifted_joins codeGen conn = testGroup "Lifted Joins"
    [ testProperty "lifted semijoin" (\a -> prop_liftsemijoin a codeGen conn)
    , testProperty "lifted antijoin" (\a -> prop_liftantijoin a codeGen conn)
    , testProperty "lifted thetajoin" (\a -> prop_liftthetajoin a codeGen conn)
    ]

tests_join_hunit :: (BackendVector b, VectorLang v) => DSHTestTree v b
tests_join_hunit codeGen conn = testGroup "HUnit joins"
    [ TH.testCase "heqjoin_nested1" (heqjoin_nested1 codeGen conn)
    , TH.testCase "hsemijoin" (hsemijoin codeGen conn)
    , TH.testCase "hsemijoin_range" (hsemijoin_range codeGen conn)
    , TH.testCase "hsemijoin_quant" (hsemijoin_quant codeGen conn)
    , TH.testCase "hsemijoin_not_null" (hsemijoin_not_null codeGen conn)
    , TH.testCase "hantijoin" (hantijoin codeGen conn)
    , TH.testCase "hantijoin_range" (hantijoin_range codeGen conn)
    , TH.testCase "hantijoin_null" (hantijoin_null codeGen conn)
    , TH.testCase "hantijoin_class12" (hantijoin_class12 codeGen conn)
    , TH.testCase "hantijoin_class15" (hantijoin_class15 codeGen conn)
    , TH.testCase "hantijoin_class16" (hantijoin_class16 codeGen conn)
    , TH.testCase "hfrontguard" (hfrontguard codeGen conn)
    ]

tests_nest_head_hunit :: (BackendVector b, VectorLang v) => DSHTestTree v b
tests_nest_head_hunit codeGen conn = testGroup "HUnit head nesting"
    [ TH.testCase "hnj1" (hnj1 codeGen conn)
    , TH.testCase "hnj2" (hnj2 codeGen conn)
    , TH.testCase "hnj3" (hnj3 codeGen conn)
    , TH.testCase "hnj4" (hnj4 codeGen conn)
    , TH.testCase "hnj5" (hnj5 codeGen conn)
    , TH.testCase "hnj6" (hnj6 codeGen conn)
    , TH.testCase "hnj7" (hnj7 codeGen conn)
    , TH.testCase "hnj8" (hnj8 codeGen conn)
    , TH.testCase "hnj9" (hnj9 codeGen conn)
    , TH.testCase "hnj10" (hnj10 codeGen conn)
    , TH.testCase "hnj11" (hnj11 codeGen conn)
    , TH.testCase "hnj12" (hnj12 codeGen conn)
    , TH.testCase "hnp1" (hnp1 codeGen conn)
    , TH.testCase "hnp2" (hnp2 codeGen conn)
    , TH.testCase "hnp3" (hnp3 codeGen conn)
    , TH.testCase "hnp4" (hnp4 codeGen conn)
    ]

tests_nest_guard_hunit :: (BackendVector b, VectorLang v) => DSHTestTree v b
tests_nest_guard_hunit codeGen conn = testGroup "HUnit guard nesting"
    [ TH.testCase "hnjg1" (hnjg1 codeGen conn)
    , TH.testCase "hnjg2" (hnjg2 codeGen conn)
    , TH.testCase "hnjg3" (hnjg3 codeGen conn)
    , TH.testCase "hnjg4" (hnjg4 codeGen conn)
    , TH.testCase "hnjg5" (hnjg5 codeGen conn)
    ]

---------------------------------------------------------------------------------
-- QuickCheck properties for comprehensions

prop_cartprod :: (BackendVector b, VectorLang v) => ([Integer], [Integer]) -> DSHProperty v b
prop_cartprod = makePropEq C.cartprod cartprod_native
  where
    cartprod_native (xs, ys) = [ (x, y) | x <- xs, y <- ys]

prop_eqjoin :: (BackendVector b, VectorLang v) => ([Integer], [Integer]) -> DSHProperty v b
prop_eqjoin = makePropEq C.eqjoin eqjoin_native
  where
    eqjoin_native (xs, ys) = [ (x, y) | x <- xs , y <- ys , x == y ]

prop_eqjoinproj :: (BackendVector b, VectorLang v) => ([Integer], [Integer]) -> DSHProperty v b
prop_eqjoinproj = makePropEq C.eqjoinproj eqjoinproj_native
  where
    eqjoinproj_native (xs, ys) = [ (x, y) | x <- xs , y <- ys , (2 * x) == y ]

prop_eqjoinpred :: (BackendVector b, VectorLang v) => (Integer, [Integer], [Integer]) -> DSHProperty v b
prop_eqjoinpred = makePropEq C.eqjoinpred eqjoinpred_native
  where
    eqjoinpred_native (x', xs, ys) = [ (x, y) | x <- xs , y <- ys , x == y , x > x']

prop_eqjointuples :: (BackendVector b, VectorLang v) => ([(Integer, Integer)], [(Integer, Integer)]) -> DSHProperty v b
prop_eqjointuples = makePropEq C.eqjointuples eqjointuples_native
  where
    eqjointuples_native (xs, ys) = [ (x1 * x2, y1, y2)
                                   | (x1, x2) <- xs
                                   , (y1, y2) <- ys
                                   , x1 == y2
                                   ]

prop_thetajoin_eq :: (BackendVector b, VectorLang v) => ([(Integer, Integer)], [(Integer, Integer)]) -> DSHProperty v b
prop_thetajoin_eq = makePropEq C.thetajoin_eq thetajoin_eq_native
  where
    thetajoin_eq_native (xs, ys) = [ (x1 * x2, y1, y2)
                                   | (x1, x2) <- xs
                                   , (y1, y2) <- ys
                                   , x1 == y2
                                   , y1 == x2
                                   ]

prop_thetajoin_neq :: (BackendVector b, VectorLang v) => ([(Integer, Integer)], [(Integer, Integer)]) -> DSHProperty v b
prop_thetajoin_neq = makePropEq C.thetajoin_neq thetajoin_neq_native
  where
    thetajoin_neq_native (xs, ys) = [ (x1 * x2, y1, y2)
                                    | (x1, x2) <- xs
                                    , (y1, y2) <- ys
                                    , x1 == y2
                                    , y1 /= x2
                                    ]


prop_eqjoin3 :: (BackendVector b, VectorLang v) => ([Integer], [Integer], [Integer]) -> DSHProperty v b
prop_eqjoin3 = makePropEq C.eqjoin3 eqjoin3_native
  where
    eqjoin3_native (xs, ys, zs) = [ (x, y, z) | x <- xs , y <- ys , z <- zs , x == y , y == z]

prop_eqjoin_nested_left :: (BackendVector b, VectorLang v) => ([(Integer, [Integer])], [Integer]) -> DSHProperty v b
prop_eqjoin_nested_left = makePropEq C.eqjoin_nested_left eqjoin_nested_left_native
  where
    eqjoin_nested_left_native (xs, ys) = [ (x, y) | x <- xs , y <- ys , fst x == y]

prop_eqjoin_nested_right :: (BackendVector b, VectorLang v) => ([Integer], [(Integer, [Integer])]) -> DSHProperty v b
prop_eqjoin_nested_right = makePropEq C.eqjoin_nested_right eqjoin_nested_right_native
  where
    eqjoin_nested_right_native (xs, ys) = [ (x, y) | x <- xs , y <- ys , x == fst y]

prop_eqjoin_nested_both :: (BackendVector b, VectorLang v) => ([(Integer, [Integer])], [(Integer, [Integer])]) -> DSHProperty v b
prop_eqjoin_nested_both = makePropEq C.eqjoin_nested_both eqjoin_nested_both_native
  where
    eqjoin_nested_both_native (xs, ys) = [ (x, y) | x <- xs , y <- ys , fst x == fst y]

prop_nestjoin :: (BackendVector b, VectorLang v) => ([Integer], [Integer]) -> DSHProperty v b
prop_nestjoin = makePropEq C.nestjoin nestjoin_native
  where
    nestjoin_native (xs, ys) = [ (x, [ y | y <- ys, x == y ]) | x <- xs]

prop_nestjoin3 :: (BackendVector b, VectorLang v) => ([Integer], [Integer], [Integer]) -> DSHProperty v b
prop_nestjoin3 = makePropEq C.nestjoin3 nestjoin3_native
  where
    nestjoin3_native (njxs, njys, njzs) =
        [ [ [ (x,y,z) | z <- njzs, y == z ]
          | y <- njys
          , x == y
          ]
        | x <- njxs
        ]

prop_groupjoin_length :: (BackendVector b, VectorLang v) => ([Integer], [Integer]) -> DSHProperty v b
prop_groupjoin_length = makePropEq C.groupjoin_length groupjoin_length_native
  where
    groupjoin_length_native (njxs, njys) =
        [ (x, fromIntegral $ length [ y | y <- njys, x == y ]) | x <- njxs ]

prop_groupjoin_length_nub :: (BackendVector b, VectorLang v) => ([Integer], [Integer]) -> DSHProperty v b
prop_groupjoin_length_nub = makePropEq C.groupjoin_length_nub groupjoin_length_nub_native
  where
    groupjoin_length_nub_native (njxs, njys) =
        [ (x, fromIntegral $ length $ nub [ y | y <- njys, x == y ]) | x <- njxs ]

prop_groupjoin_sum :: (BackendVector b, VectorLang v) => ([Integer], [Integer]) -> DSHProperty v b
prop_groupjoin_sum = makePropEq C.groupjoin_sum groupjoin_sum_native
  where
    groupjoin_sum_native (njxs, njys) =
        [ (x, fromIntegral $ sum [ 2 * y + x | y <- njys, x == y ]) | x <- njxs ]

prop_groupjoin_sum2 :: (BackendVector b, VectorLang v) => ([Integer], [Integer]) -> DSHProperty v b
prop_groupjoin_sum2 = makePropEq C.groupjoin_sum2 groupjoin_sum2_native
  where
    groupjoin_sum2_native (njxs, njys) =
        [ x + fromIntegral (sum [ 2 * y | y <- njys, x == y ]) | x <- njxs ]

prop_groupjoin_sum_length :: (BackendVector b, VectorLang v) => ([Integer], [Integer]) -> DSHProperty v b
prop_groupjoin_sum_length = makePropEq C.groupjoin_sum_length groupjoin_sum_length_native
  where
    groupjoin_sum_length_native (njxs, njys) =
        [ ( x
          , fromIntegral $ sum [ 2 * y | y <- njys, x == y ]
          , fromIntegral $ length [ y | y <- njys, x == y ]
          )
        | x <- njxs
        ]

prop_groupjoin_sum_length2 :: (BackendVector b, VectorLang v) => ([Integer], [Integer]) -> DSHProperty v b
prop_groupjoin_sum_length2 = makePropEq C.groupjoin_sum_length2 groupjoin_sum_length2_native
  where
    groupjoin_sum_length2_native (njxs, njys) =
        [ ( x
          , fromIntegral $ sum [ 2 * y | y <- njys, x == y ]
          , fromIntegral $ length [ y | y <- njys, x == y ]
          )
        | x <- njxs
        , 20 < sum [ 3 + y | y <- njys, x == y ]
        ]

prop_groupjoin_sum_deep :: (BackendVector b, VectorLang v) => ([Integer], [Integer], [Integer]) -> DSHProperty v b
prop_groupjoin_sum_deep = makePropEq C.groupjoin_sum_deep groupjoin_sum_deep_native
  where
    groupjoin_sum_deep_native (njxs, njys, njzs) =
        [ [ (x, fromIntegral $ sum [ 2 * y | y <- njys, x == y ]) | x <- njxs, x == z ]
        | z <- njzs
        ]

prop_groupjoin_length_guard :: (BackendVector b, VectorLang v) => ([Integer], [Integer]) -> DSHProperty v b
prop_groupjoin_length_guard = makePropEq C.groupjoin_sum_guard groupjoin_length_guard_native
  where
    groupjoin_length_guard_native (njxs, njys) =
        [ x
        | x <- njxs
        , let ys = [ 2 * y | y <- njys, x == y ]
        , 5 < length ys
        ]

prop_groupjoin_length_guard2 :: (BackendVector b, VectorLang v) => ([Integer], [Integer]) -> DSHProperty v b
prop_groupjoin_length_guard2 = makePropEq C.groupjoin_sum_guard2 groupjoin_sum_guard2_native
  where
    groupjoin_sum_guard2_native (njxs, njys) =
        [ (x, fromIntegral $ sum ys)
        | x <- njxs
        , let ys = [ 2 * y | y <- njys, x == y ]
        , 5 < length ys
        ]

prop_groupjoin_sum_nest :: (BackendVector b, VectorLang v) => ([Integer], [Integer]) -> DSHProperty v b
prop_groupjoin_sum_nest = makePropEq C.groupjoin_sum_nest groupjoin_sum_nest_native
  where
    groupjoin_sum_nest_native (njxs, njys) =
        [ (x, fromIntegral $ sum ys, ys)
        | x <- njxs
        , let ys = [ 2 * y | y <- njys, x == y ]
        ]

prop_groupjoin_sum_nest2 :: (BackendVector b, VectorLang v) => ([Integer], [Integer]) -> DSHProperty v b
prop_groupjoin_sum_nest2 = makePropEq C.groupjoin_sum_nest2 groupjoin_sum_nest2_native
  where
    groupjoin_sum_nest2_native (njxs, njys) =
        [ (x, fromIntegral $ sum ys, ys)
        | x <- njxs
        , let ys = [ x + 2 * y | y <- njys, x == y ]
        , 10 > length ys
        ]

prop_groupjoin_nestjoin :: (BackendVector b, VectorLang v) => ([Integer], [Integer], [Integer]) -> DSHProperty v b
prop_groupjoin_nestjoin = makePropEq C.groupjoin_nestjoin groupjoin_nestjoin_native
  where
    groupjoin_nestjoin_native (njxs, njys, njzs) =
        [ (x, fromIntegral $ sum [ 2 * y | y <- njys, x == y ], [ z + 10 | z <- njzs, z > x ])
        | x <- njxs
        ]

prop_groupjoin_nestjoin_guard :: (BackendVector b, VectorLang v) => ([Integer], [Integer], [Integer]) -> DSHProperty v b
prop_groupjoin_nestjoin_guard = makePropEq C.groupjoin_nestjoin_guard groupjoin_nestjoin_guard_native
  where
    groupjoin_nestjoin_guard_native (njxs, njys, njzs) =
        [ (x, fromIntegral $ sum [ 2 * y | y <- njys, x == y ], [ z + 10 | z <- njzs, z > x ])
        | x <- njxs
        , 10 < length [ y | y <- njys, x == y ]
        ]

prop_groupjoin_length_deep_sum :: (BackendVector b, VectorLang v) => ([Integer], [Integer], [Integer]) -> DSHProperty v b
prop_groupjoin_length_deep_sum = makePropEq C.groupjoin_length_deep_sum groupjoin_length_deep_sum_native
  where
    groupjoin_length_deep_sum_native (njxs, njys, njzs) =
        [ z + sum [ fromIntegral $ length [ 2 * y + x | y <- njys, x == y ] | x <- njxs, x == z ]
        | z <- njzs
        ]

prop_aj_class12 :: (BackendVector b, VectorLang v) => ([Integer], [Integer]) -> DSHProperty v b
prop_aj_class12 = makePropEq C.aj_class12 aj_class12_native
  where
    aj_class12_native (ajxs, ajys) = [ x
                                     | x <- ajxs
                                     , and [ x == y | y <- ajys, y > 10 ]
                                     ]

prop_aj_class15 :: (BackendVector b, VectorLang v) => ([Integer], [Integer]) -> DSHProperty v b
prop_aj_class15 = makePropEq C.aj_class15 aj_class15_native
  where
    aj_class15_native (ajxs, ajys) = [ x
                                     | x <- ajxs
                                     , and [ y `rem` 4 == 0 | y <- ajys, x < y ]
                                     ]

prop_aj_class16 :: (BackendVector b, VectorLang v) => ([Integer], [Integer]) -> DSHProperty v b
prop_aj_class16 = makePropEq C.aj_class16 aj_class16_native
  where
    aj_class16_native (ajxs, ajys) = [ x
                                     | x <- ajxs
                                     , and [ y <= 2 * x | y <- ajys, x < y ]
                                     ]

prop_backdep :: (BackendVector b, VectorLang v) => [[Integer]] -> DSHProperty v b
prop_backdep = makePropEq C.backdep backdep_native
  where
    backdep_native xss = [x | xs <- xss, x <- xs]

prop_backdep_filter :: (BackendVector b, VectorLang v) => [[Integer]] -> DSHProperty v b
prop_backdep_filter = makePropEq C.backdep_filter backdep_filter_native
  where
    backdep_filter_native xss = [x | xs <- xss, x <- xs, fromIntegral (length xs) > x]

prop_backdep2 :: (BackendVector b, VectorLang v) => [[Integer]] -> DSHProperty v b
prop_backdep2 = makePropEq C.backdep2 backdep2
  where
    backdep2 xss = [ [ x * 42 | x <- xs ] | xs <- xss ]

prop_backdep3 :: (BackendVector b, VectorLang v) => [[Integer]] -> DSHProperty v b
prop_backdep3 = makePropEq C.backdep3 backdep3
  where
    backdep3 xss = [ [ x + fromIntegral (length xs) | x <- xs ] | xs <- xss ]

prop_backdep4 :: (BackendVector b, VectorLang v) => [[[Integer]]] -> DSHProperty v b
prop_backdep4 = makePropEq C.backdep4 backdep4
  where
    backdep4 xsss = [ [ [ x + fromIntegral (length xs) + fromIntegral (length xss)
                        | x <- xs
                        ]
                      | xs <- xss
                      ]
                    | xss <- xsss
                    ]

prop_backdep5 :: (BackendVector b, VectorLang v) => [[Integer]] -> DSHProperty v b
prop_backdep5 = makePropEq C.backdep5 backdep5
  where
    backdep5 xss = [ [ x + fromIntegral (length xs)
                     | x <- take (length xs - 3) xs ]
                   | xs <- xss ]

--------------------------------------------------------------------------------
-- Property tests for join operators in combination with guards and filters

prop_njg6 :: (BackendVector b, VectorLang v) => ([Integer], [Integer], [Integer]) -> DSHProperty v b
prop_njg6 = makePropEq (\(Q.view -> (xs, ys, zs)) -> C.njg6 xs ys zs)
                       (\(xs, ys, zs) -> njg6 xs ys zs)

prop_njg7 :: (BackendVector b, VectorLang v) => ([Integer], [Integer], [Integer]) -> DSHProperty v b
prop_njg7 = makePropEq (\(Q.view -> (xs, ys, zs)) -> C.njg7 xs ys zs)
                       (\(xs, ys, zs) -> njg7 xs ys zs)

--------------------------------------------------------------------------------
-- Tests for lifted join operators

prop_liftsemijoin :: (BackendVector b, VectorLang v) => ([Positive Integer], [Integer]) -> DSHProperty v b
prop_liftsemijoin (xs, ys) = makePropEq C.liftsemijoin liftsemijoin (xs', ys)
  where
    xs' = map getPositive xs

liftsemijoin :: ([Integer], [Integer]) -> [[Integer]]
liftsemijoin (xs, ys) =
    [ [ x | x <- g, x `elem` ys ]
    | g <- groupWith (`rem` 10) xs
    ]

prop_liftantijoin :: (BackendVector b, VectorLang v) => ([Positive Integer], [Integer]) -> DSHProperty v b
prop_liftantijoin (xs, ys) = makePropEq C.liftantijoin liftantijoin (xs', ys)
  where
    xs' = map getPositive xs

liftantijoin :: ([Integer], [Integer]) -> [[Integer]]
liftantijoin (xs, ys) =
    [ [ x | x <- g, x `notElem` ys ]
    | g <- groupWith (`rem` 10) xs
    ]

prop_liftthetajoin :: (BackendVector b, VectorLang v) => ([Positive Integer], [Integer]) -> DSHProperty v b
prop_liftthetajoin (xs, ys) = makePropEq C.liftthetajoin liftthetajoin (xs', ys)
  where
    xs' = map getPositive xs

liftthetajoin :: ([Integer], [Integer]) -> [[(Integer, Integer)]]
liftthetajoin (xs, ys) =
    [ [ (x, y) | x <- g, y <- ys, x < y ]
    | g <- groupWith (`rem` 10) xs
    ]

-----------------------------------------------------------------------
-- HUnit tests for comprehensions

heqjoin_nested1 :: (BackendVector b, VectorLang v) => DSHAssertion v b
heqjoin_nested1 = makeEqAssertion "heqjoin_nested" C.eqjoin_nested1 res
  where
    res = [ ((20, ['b']), 20)
          , ((30, ['c', 'd']), 30)
          , ((30, ['c', 'd']), 30)
          , ((40, []), 40)
          ]

hsemijoin :: (BackendVector b, VectorLang v) => DSHAssertion v b
hsemijoin = makeEqAssertion "hsemijoin" C.semijoin res
  where
    res = [2, 4, 6, 7]

hsemijoin_range :: (BackendVector b, VectorLang v) => DSHAssertion v b
hsemijoin_range = makeEqAssertion "hsemijoin_range" C.semijoin_range res
  where
    res = [2, 4]

hsemijoin_not_null :: (BackendVector b, VectorLang v) => DSHAssertion v b
hsemijoin_not_null = makeEqAssertion "hsemijoin_range" C.semijoin_not_null res
  where
    res = [2, 4, 6, 7]

hsemijoin_quant :: (BackendVector b, VectorLang v) => DSHAssertion v b
hsemijoin_quant = makeEqAssertion "hsemijoin_quant" C.semijoin_quant res
  where
    res = [6,7]

hantijoin :: (BackendVector b, VectorLang v) => DSHAssertion v b
hantijoin = makeEqAssertion "hantijoin" C.antijoin res
  where
    res = [1, 3, 5]

hantijoin_range :: (BackendVector b, VectorLang v) => DSHAssertion v b
hantijoin_range = makeEqAssertion "hantijoin_range" C.antijoin_range res
  where
    res = [1, 3, 5, 6, 7]

hantijoin_null :: (BackendVector b, VectorLang v) => DSHAssertion v b
hantijoin_null = makeEqAssertion "hantijoin_range" C.antijoin_null res
  where
    res = [1, 3, 5]

hantijoin_class12 :: (BackendVector b, VectorLang v) => DSHAssertion v b
hantijoin_class12 = makeEqAssertion "hantijoin_class12" C.antijoin_class12 res
  where
    res = [6,7,8,9,10]

hantijoin_class15 :: (BackendVector b, VectorLang v) => DSHAssertion v b
hantijoin_class15 = makeEqAssertion "hantijoin_class15" C.antijoin_class15 res
  where
    res = [5,6,7,8]

hantijoin_class16 :: (BackendVector b, VectorLang v) => DSHAssertion v b
hantijoin_class16 = makeEqAssertion "hantijoin_class16" C.antijoin_class16 res
  where
    res = [4,5,6]

hfrontguard :: (BackendVector b, VectorLang v) => DSHAssertion v b
hfrontguard = makeEqAssertion "hfrontguard" C.frontguard res
  where
    res = [[],[1,2],[1,2]]

-----------------------------------------------------------------------
-- HUnit tests for nestjoin/nestproduct

njxs1 :: [Integer]
njxs1 = [1,2,3,4,5,6]

njys1 :: [Integer]
njys1 = [3,4,5,6,3,6,4,1,1,1]

hnj1 :: (BackendVector b, VectorLang v) => DSHAssertion v b
hnj1 = makeEqAssertion "hnj1" (C.nj1 njxs1 njys1) (nj1 njxs1 njys1)

hnj2 :: (BackendVector b, VectorLang v) => DSHAssertion v b
hnj2 = makeEqAssertion "hnj2" (C.nj2 njxs1 njys1) (nj2 njxs1 njys1)

hnj3 :: (BackendVector b, VectorLang v) => DSHAssertion v b
hnj3 = makeEqAssertion "hnj3" (C.nj3 njxs1 njys1) (nj3 njxs1 njys1)

hnj4 :: (BackendVector b, VectorLang v) => DSHAssertion v b
hnj4 = makeEqAssertion "hnj4" (C.nj4 njxs1 njys1) (nj4 njxs1 njys1)

hnj5 :: (BackendVector b, VectorLang v) => DSHAssertion v b
hnj5 = makeEqAssertion "hnj5" (C.nj5 njxs1 njys1) (nj5 njxs1 njys1)

hnj6 :: (BackendVector b, VectorLang v) => DSHAssertion v b
hnj6 = makeEqAssertion "hnj6" (C.nj6 njxs1 njys1) (nj6 njxs1 njys1)

hnj7 :: (BackendVector b, VectorLang v) => DSHAssertion v b
hnj7 = makeEqAssertion "hnj7" (C.nj7 njxs1 njys1) (nj7 njxs1 njys1)

hnj8 :: (BackendVector b, VectorLang v) => DSHAssertion v b
hnj8 = makeEqAssertion "hnj8" (C.nj8 njxs1 njys1) (nj8 njxs1 njys1)

hnj9 :: (BackendVector b, VectorLang v) => DSHAssertion v b
hnj9 = makeEqAssertion "hnj9" (C.nj9 njxs1 njys1) (nj9 njxs1 njys1)

hnj10 :: (BackendVector b, VectorLang v) => DSHAssertion v b
hnj10 = makeEqAssertion "hnj10" (C.nj10 njxs1 njys1) (nj10 njxs1 njys1)

hnj11 :: (BackendVector b, VectorLang v) => DSHAssertion v b
hnj11 = makeEqAssertion "hnj11" (C.nj11 njxs1 njys1) (nj11 njxs1 njys1)

-- Test data for testcase hnj12
njxs2, njys2, njzs2 :: [Integer]
njxs2 = [1,2,3,4,5,5,2]
njys2 = [2,1,0,5,4,4,4]
njzs2 = [6,1,1,3,2,5]

hnj12 :: (BackendVector b, VectorLang v) => DSHAssertion v b
hnj12 = makeEqAssertion "hnj12" (C.nj12 njxs2 njys2 njzs2) (nj12 njxs2 njys2 njzs2)

hnp1 :: (BackendVector b, VectorLang v) => DSHAssertion v b
hnp1 = makeEqAssertion "hnp1" (C.np1 njxs1 njys1) (np1 njxs1 njys1)

hnp2 :: (BackendVector b, VectorLang v) => DSHAssertion v b
hnp2 = makeEqAssertion "hnp2" (C.np2 njxs1 njys1) (np2 njxs1 njys1)

hnp3 :: (BackendVector b, VectorLang v) => DSHAssertion v b
hnp3 = makeEqAssertion "hnp3" (C.np3 njxs1 njys1) (np3 njxs1 njys1)

hnp4 :: (BackendVector b, VectorLang v) => DSHAssertion v b
hnp4 = makeEqAssertion "hnp4" (C.np4 njxs1 njys1) (np4 njxs1 njys1)

hnjg1 :: (BackendVector b, VectorLang v) => DSHAssertion v b
hnjg1 = makeEqAssertion "hnjg1" (C.njg1 njgxs1 njgzs1) (njg1 njgxs1 njgzs1)

hnjg2 :: (BackendVector b, VectorLang v) => DSHAssertion v b
hnjg2 = makeEqAssertion "hnjg2" (C.njg2 njgxs1 njgys1) (njg2 njgxs1 njgys1)

hnjg3 :: (BackendVector b, VectorLang v) => DSHAssertion v b
hnjg3 = makeEqAssertion "hnjg3" (C.njg3 njgxs1 njgys1 njgzs1) (njg3 njgxs1 njgys1 njgzs1)

hnjg4 :: (BackendVector b, VectorLang v) => DSHAssertion v b
hnjg4 = makeEqAssertion "hnjg4" (C.njg4 njgxs1 njgys1 njgzs1) (njg4 njgxs1 njgys1 njgzs1)

hnjg5 :: (BackendVector b, VectorLang v) => DSHAssertion v b
hnjg5 = makeEqAssertion "hnjg5" (C.njg5 njgxs1 njgys1) (njg5 njgxs1 njgys1)

pair :: a -> b -> (a, b)
pair = (,)

-- Head/NestJoin
nj1 :: [Integer] -> [Integer] -> [[Integer]]
nj1 njxs njys =
    [ [ y | y <- njys, x == y ]
    | x <- njxs
    ]

nj2 :: [Integer] -> [Integer] -> [(Integer, [Integer])]
nj2 njxs njys =
    [ pair x [ y | y <- njys, x == y ]
    | x <- njxs
    ]

nj3 :: [Integer] -> [Integer] -> [(Integer, [Integer])]
nj3 njxs njys =
    [ pair x ([ y | y <- njys, x == y ] ++ [100, 200, 300])
    | x <- njxs
    ]

nj4 :: [Integer] -> [Integer] -> [(Integer, [Integer])]
nj4 njxs njys =
      [ pair x ([ y | y <- njys, x == y ] ++ [ z | z <- njys, x == z ])
      | x <- njxs
      ]

nj5 :: [Integer] -> [Integer] -> [(Integer, [Integer])]
nj5 njxs njys =
      [ pair x [ y | y <- njys, x + y > 15 ]
      | x <- njxs
      ]

nj6 :: [Integer] -> [Integer] -> [(Integer, [Integer])]
nj6 njxs njys =
      [ pair x [ y | y <- njys, x + y > 10, y < 7 ]
      | x <- njxs
      ]

nj7 :: [Integer] -> [Integer] -> [[Integer]]
nj7 njxs njys =
    [ [ x + y | y <- njys, x + 2 == y ] | x <- njxs ]

nj8 :: [Integer] -> [Integer] -> [[Integer]]
nj8 njxs njys = [ [ x + y | y <- njys, x == y, y < 5 ] | x <- njxs, x > 3 ]

nj9 :: [Integer] -> [Integer] -> [[Integer]]
nj9 njxs njys = [ [ x + y | y <- njys, x + 1 == y, y > 2, x < 6 ] | x <- njxs ]

nj10 :: [Integer] -> [Integer] -> [Integer]
nj10 njxs njys = [ x + sum [ x * y | y <- njys, x == y ] | x <- njxs ]

nj11 :: [Integer] -> [Integer] -> [[Integer]]
nj11 njxs njys = [ [ x + y | y <- njys, x > y, x < y * 2 ] | x <- njxs ]

nj12 :: [Integer] -> [Integer] -> [Integer] -> [[[(Integer, Integer, Integer)]]]
nj12 njxs njys njzs =
    [ [ [ (x,y,z) | z <- njzs, y == z ]
      | y <- njys
      , x == y
      ]
    | x <- njxs
    ]

-- Head/NestProduct
np1 :: [Integer] -> [Integer] -> [[Integer]]
np1 njxs njys = [ [ x * y * 2 | y <- njys ] | x <- njxs ]

np2 :: [Integer] -> [Integer] -> [(Integer, [Integer])]
np2 njxs njys = [ pair x [ y * 2 | y <- njys ] | x <- njxs ]

np3 :: [Integer] -> [Integer] -> [[Integer]]
np3 njxs njys = [ [ x + y | y <- njys ] | x <- njxs ]

np4 :: [Integer] -> [Integer] -> [[Integer]]
np4 njxs njys = [ [ y | y <- njys, x > y ] | x <- njxs ]

-- Guard/NestJoin

njgxs1 :: [Integer]
njgxs1 = [1,2,3,4,5,6,7,8,12]

njgys1 :: [Integer]
njgys1 = [2,3,2,4,5,5,9,12,2,2,13]

njgzs1 :: [(Integer, Integer)]
njgzs1 = [(2, 20), (5, 60), (3, 30), (3, 80), (4, 40), (5, 10), (5, 30), (12, 120)]

njg1 :: [Integer] -> [(Integer, Integer)] -> [Integer]
njg1 njgxs njgzs =
  [ x
  | x <- njgxs
  , x < 8
  , sum [ snd z | z <- njgzs, fst z == x ] > 100
  ]

njg2 :: [Integer] -> [Integer] -> [Integer]
njg2 njgxs njgys =
  [ x
  | x <- njgxs
  , and [ y > 1 | y <- njgys, x == y ]
  , x < 8
  ]

njg3 :: [Integer] -> [Integer] -> [(Integer, Integer)] -> [(Integer, Integer)]
njg3 njgxs njgys njgzs =
  [ pair x y
  | x <- njgxs
  , y <- njgys
  , length [ () | z <- njgzs, fst z == x ] > 2
  ]

njg4 :: [Integer] -> [Integer] -> [(Integer, Integer)] -> [Integer]
njg4 njgxs njgys njgzs =
  [ x
  | x <- njgxs
  , length [ () | y <- njgys, x == y ]
    > length [ () | z <- njgzs, fst z == x ]
  ]

njg5 :: [Integer] -> [Integer] -> [Integer]
njg5 njgxs njgys =
  [ x
  | x <- njgxs
  , sum [ y | y <- njgys, x < y, y > 5 ] < 10
  ]

njg6 :: [Integer] -> [Integer] -> [Integer] -> [(Integer, [Integer])]
njg6 njgxs njgys njgzs =
    [ (x, [ y | y <- njgys, x == y ])
    | x <- njgxs
    , x `elem` njgzs
    ]

njg7 :: [Integer] -> [Integer] -> [Integer] -> [(Integer, [Integer])]
njg7 njgxs njgys njgzs =
    filter ((`elem` njgzs) . fst)
    [ (x, [ y | y <- njgys, x == y ])
    | x <- njgxs
    ]

--------------------------------------------------------------------------------
--

prop_deep_iter :: (BackendVector b, VectorLang v) => ([Integer], [Integer], [Integer], [Integer], [Integer]) -> DSHProperty v b
prop_deep_iter = makePropEq C.deep_iter deep_iter_native
  where
    deep_iter_native (ws1, ws2, xs, ys, zs) =
      [ [ [ [ w1 * 23 - y | w1 <- ws1 ]
            ++
            [ w2 + 42 - y | w2 <- ws2 ]
          | z <- zs
          , z > x
          ]
        | y <- ys
        ]
      | x <- xs
      ]

-- | Test non-lifted tuple construction with a singleton extracted
-- from a nested list.
prop_only_tuple :: (BackendVector b, VectorLang v)
                => (Integer, NonEmptyList Integer, [Integer])
                -> DSHProperty v b
prop_only_tuple (x, ys, zs) =
    makePropEq C.only_tuple only_tuple (x, getNonEmpty ys, zs)

only_tuple :: (Integer, [Integer], [Integer]) -> (Integer, (Integer, [Integer]))
only_tuple (x, ys, zs) =
    pair x (head [ (y, [ z | z <- zs, x == y ])  | y <- ys ])
