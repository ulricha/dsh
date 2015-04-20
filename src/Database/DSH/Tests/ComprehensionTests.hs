-- | Tests on certain aspects of comprehension nesting.
module Database.DSH.Tests.ComprehensionTests
    ( tests_comprehensions
    , tests_lifted_joins
    , tests_join_hunit
    , tests_nest_head_hunit
    , tests_nest_guard_hunit
    ) where

import           GHC.Exts

import           Test.Framework                       (Test, testGroup)
import           Test.Framework.Providers.HUnit
import           Test.Framework.Providers.QuickCheck2 (testProperty)
import           Test.HUnit                           (Assertion)
import           Test.QuickCheck

import           Database.DSH.Backend
import           Database.DSH.Tests.Common
import qualified Database.DSH.Tests.DSHComprehensions as C


tests_comprehensions :: Backend c => c -> Test
tests_comprehensions conn = testGroup "Comprehensions"
    [ testProperty "cartprod" (\a -> prop_cartprod a conn)
    , testProperty "eqjoin" (\a -> prop_eqjoin a conn)
    , testProperty "eqjoinproj" (\a -> prop_eqjoinproj a conn)
    , testProperty "eqjoinpred" (\a -> prop_eqjoinpred a conn)
    , testProperty "eqjointuples" (\a -> prop_eqjointuples a conn)
    , testProperty "thetajoin_eq" (\a -> prop_thetajoin_eq a conn)
    , testProperty "thetajoin_neq" (\a -> prop_thetajoin_neq a conn)
    , testProperty "eqjoin3" (\a -> prop_eqjoin3 a conn)
    , testProperty "eqjoin_nested_left" (\a -> prop_eqjoin_nested_left a conn)
    , testProperty "eqjoin_nested_right" (\a -> prop_eqjoin_nested_right a conn)
    , testProperty "eqjoin_nested_both" (\a -> prop_eqjoin_nested_both a conn)
    , testProperty "nestjoin" (\a -> prop_nestjoin a conn)
    , testProperty "nestjoin3" (\a -> prop_nestjoin3 a conn)
    , testProperty "groupjoin length" (\a -> prop_groupjoin_length a conn)
    , testProperty "antijoin class12" (\a -> prop_aj_class12 a conn)
    , testProperty "antijoin class15" (\a -> prop_aj_class15 a conn)
    , testProperty "antijoin class16" (\a -> prop_aj_class16 a conn)
    , testProperty "backdep1" (\a -> prop_backdep a conn)
    , testProperty "backdep_filter" (\a -> prop_backdep_filter a conn)
    , testProperty "backdep2" (\a -> prop_backdep2 a conn)
    , testProperty "backdep3" (\a -> prop_backdep3 a conn)
    , testProperty "backdep4" (\a -> prop_backdep4 a conn)
    , testProperty "backdep5" (\a -> prop_backdep5 a conn)
    , testProperty "deep" (\a -> prop_deep_iter a conn)
    , testProperty "only tuple" (\a -> prop_only_tuple a conn)
    ]

tests_lifted_joins :: Backend c => c -> Test
tests_lifted_joins conn = testGroup "Lifted Joins"
    [ testProperty "lifted semijoin" (\a -> prop_liftsemijoin a conn)
    , testProperty "lifted antijoin" (\a -> prop_liftantijoin a conn)
    , testProperty "lifted thetajoin" (\a -> prop_liftthetajoin a conn)
    ]

tests_join_hunit :: Backend c => c -> Test
tests_join_hunit conn = testGroup "HUnit joins"
    [ testCase "heqjoin_nested1" (heqjoin_nested1 conn)
    , testCase "hsemijoin" (hsemijoin conn)
    , testCase "hsemijoin_range" (hsemijoin_range conn)
    , testCase "hsemijoin_quant" (hsemijoin_quant conn)
    , testCase "hsemijoin_not_null" (hsemijoin_not_null conn)
    , testCase "hantijoin" (hantijoin conn)
    , testCase "hantijoin_range" (hantijoin_range conn)
    , testCase "hantijoin_null" (hantijoin_null conn)
    , testCase "hantijoin_class12" (hantijoin_class12 conn)
    , testCase "hantijoin_class15" (hantijoin_class15 conn)
    , testCase "hantijoin_class16" (hantijoin_class16 conn)
    , testCase "hfrontguard" (hfrontguard conn)
    ]

tests_nest_head_hunit :: Backend c => c -> Test
tests_nest_head_hunit conn = testGroup "HUnit head nesting"
    [ testCase "hnj1" (hnj1 conn)
    , testCase "hnj2" (hnj2 conn)
    , testCase "hnj3" (hnj3 conn)
    , testCase "hnj4" (hnj4 conn)
    , testCase "hnj5" (hnj5 conn)
    , testCase "hnj6" (hnj6 conn)
    , testCase "hnj7" (hnj7 conn)
    , testCase "hnj8" (hnj8 conn)
    , testCase "hnj9" (hnj9 conn)
    , testCase "hnj10" (hnj10 conn)
    , testCase "hnj11" (hnj11 conn)
    , testCase "hnj12" (hnj12 conn)
    , testCase "hnp1" (hnp1 conn)
    , testCase "hnp2" (hnp2 conn)
    , testCase "hnp3" (hnp3 conn)
    , testCase "hnp4" (hnp4 conn)
    ]

tests_nest_guard_hunit :: Backend c => c -> Test
tests_nest_guard_hunit conn = testGroup "HUnit guard nesting"
    [ testCase "hnjg1" (hnjg1 conn)
    , testCase "hnjg2" (hnjg2 conn)
    , testCase "hnjg3" (hnjg3 conn)
    , testCase "hnjg4" (hnjg4 conn)
    , testCase "hnjg5" (hnjg5 conn)
    ]

---------------------------------------------------------------------------------
-- QuickCheck properties for comprehensions

prop_cartprod :: Backend c => ([Integer], [Integer]) -> c -> Property
prop_cartprod = makePropEq C.cartprod cartprod_native
  where
    cartprod_native (xs, ys) = [ (x, y) | x <- xs, y <- ys]

prop_eqjoin :: Backend c => ([Integer], [Integer]) -> c -> Property
prop_eqjoin = makePropEq C.eqjoin eqjoin_native
  where
    eqjoin_native (xs, ys) = [ (x, y) | x <- xs , y <- ys , x == y ]

prop_eqjoinproj :: Backend c => ([Integer], [Integer]) -> c -> Property
prop_eqjoinproj = makePropEq C.eqjoinproj eqjoinproj_native
  where
    eqjoinproj_native (xs, ys) = [ (x, y) | x <- xs , y <- ys , (2 * x) == y ]

prop_eqjoinpred :: Backend c => (Integer, [Integer], [Integer]) -> c -> Property
prop_eqjoinpred = makePropEq C.eqjoinpred eqjoinpred_native
  where
    eqjoinpred_native (x', xs, ys) = [ (x, y) | x <- xs , y <- ys , x == y , x > x']

prop_eqjointuples :: Backend c => ([(Integer, Integer)], [(Integer, Integer)]) -> c -> Property
prop_eqjointuples = makePropEq C.eqjointuples eqjointuples_native
  where
    eqjointuples_native (xs, ys) = [ (x1 * x2, y1, y2)
                                   | (x1, x2) <- xs
                                   , (y1, y2) <- ys
                                   , x1 == y2
                                   ]

prop_thetajoin_eq :: Backend c => ([(Integer, Integer)], [(Integer, Integer)]) -> c -> Property
prop_thetajoin_eq = makePropEq C.thetajoin_eq thetajoin_eq_native
  where
    thetajoin_eq_native (xs, ys) = [ (x1 * x2, y1, y2)
                                   | (x1, x2) <- xs
                                   , (y1, y2) <- ys
                                   , x1 == y2
                                   , y1 == x2
                                   ]

prop_thetajoin_neq :: Backend c => ([(Integer, Integer)], [(Integer, Integer)]) -> c -> Property
prop_thetajoin_neq = makePropEq C.thetajoin_neq thetajoin_neq_native
  where
    thetajoin_neq_native (xs, ys) = [ (x1 * x2, y1, y2)
                                    | (x1, x2) <- xs
                                    , (y1, y2) <- ys
                                    , x1 == y2
                                    , y1 /= x2
                                    ]


prop_eqjoin3 :: Backend c => ([Integer], [Integer], [Integer]) -> c -> Property
prop_eqjoin3 = makePropEq C.eqjoin3 eqjoin3_native
  where
    eqjoin3_native (xs, ys, zs) = [ (x, y, z) | x <- xs , y <- ys , z <- zs , x == y , y == z]

prop_eqjoin_nested_left :: Backend c => ([(Integer, [Integer])], [Integer]) -> c -> Property
prop_eqjoin_nested_left = makePropEq C.eqjoin_nested_left eqjoin_nested_left_native
  where
    eqjoin_nested_left_native (xs, ys) = [ (x, y) | x <- xs , y <- ys , fst x == y]

prop_eqjoin_nested_right :: Backend c => ([Integer], [(Integer, [Integer])]) -> c -> Property
prop_eqjoin_nested_right = makePropEq C.eqjoin_nested_right eqjoin_nested_right_native
  where
    eqjoin_nested_right_native (xs, ys) = [ (x, y) | x <- xs , y <- ys , x == fst y]

prop_eqjoin_nested_both :: Backend c => ([(Integer, [Integer])], [(Integer, [Integer])]) -> c -> Property
prop_eqjoin_nested_both = makePropEq C.eqjoin_nested_both eqjoin_nested_both_native
  where
    eqjoin_nested_both_native (xs, ys) = [ (x, y) | x <- xs , y <- ys , fst x == fst y]

prop_nestjoin :: Backend c => ([Integer], [Integer]) -> c -> Property
prop_nestjoin = makePropEq C.nestjoin nestjoin_native
  where
    nestjoin_native (xs, ys) = [ (x, [ y | y <- ys, x == y ]) | x <- xs]

prop_nestjoin3 :: Backend c => ([Integer], [Integer], [Integer]) -> c -> Property
prop_nestjoin3 = makePropEq C.nestjoin3 nestjoin3_native
  where
    nestjoin3_native (njxs, njys, njzs) =
        [ [ [ (x,y,z) | z <- njzs, y == z ]
          | y <- njys
          , x == y
          ]
        | x <- njxs
        ]

prop_groupjoin_length :: Backend c => ([Integer], [Integer]) -> c -> Property
prop_groupjoin_length = makePropEq C.groupjoin_length groupjoin_length_native
  where
    groupjoin_length_native (njxs, njys) =
        [ (x, fromIntegral $ length [ y | y <- njys, x == y ]) | x <- njxs ]

prop_aj_class12 :: Backend c => ([Integer], [Integer]) -> c -> Property
prop_aj_class12 = makePropEq C.aj_class12 aj_class12_native
  where
    aj_class12_native (ajxs, ajys) = [ x
                                     | x <- ajxs
                                     , and [ x == y | y <- ajys, y > 10 ]
                                     ]

prop_aj_class15 :: Backend c => ([Integer], [Integer]) -> c -> Property
prop_aj_class15 = makePropEq C.aj_class15 aj_class15_native
  where
    aj_class15_native (ajxs, ajys) = [ x
                                     | x <- ajxs
                                     , and [ y `mod` 4 == 0 | y <- ajys, x < y ]
                                     ]

prop_aj_class16 :: Backend c => ([Integer], [Integer]) -> c -> Property
prop_aj_class16 = makePropEq C.aj_class16 aj_class16_native
  where
    aj_class16_native (ajxs, ajys) = [ x
                                     | x <- ajxs
                                     , and [ y <= 2 * x | y <- ajys, x < y ]
                                     ]

prop_backdep :: Backend c => [[Integer]] -> c -> Property
prop_backdep = makePropEq C.backdep backdep_native
  where
    backdep_native xss = [x | xs <- xss, x <- xs]

prop_backdep_filter :: Backend c => [[Integer]] -> c -> Property
prop_backdep_filter = makePropEq C.backdep_filter backdep_filter_native
  where
    backdep_filter_native xss = [x | xs <- xss, x <- xs, fromIntegral (length xs) > x]

prop_backdep2 :: Backend c => [[Integer]] -> c -> Property
prop_backdep2 = makePropEq C.backdep2 backdep2
  where
    backdep2 xss = [ [ x * 42 | x <- xs ] | xs <- xss ]

prop_backdep3 :: Backend c => [[Integer]] -> c -> Property
prop_backdep3 = makePropEq C.backdep3 backdep3
  where
    backdep3 xss = [ [ x + fromIntegral (length xs) | x <- xs ] | xs <- xss ]

prop_backdep4 :: Backend c => [[[Integer]]] -> c -> Property
prop_backdep4 = makePropEq C.backdep4 backdep4
  where
    backdep4 xsss = [ [ [ x + fromIntegral (length xs) + fromIntegral (length xss)
                        | x <- xs
                        ]
                      | xs <- xss
                      ]
                    | xss <- xsss
                    ]

prop_backdep5 :: Backend c => [[Integer]] -> c -> Property
prop_backdep5 = makePropEq C.backdep5 backdep5
  where
    backdep5 xss = [ [ x + fromIntegral (length xs)
                     | x <- take (length xs - 3) xs ]
                   | xs <- xss ]

--------------------------------------------------------------------------------
-- Tests for lifted join operators

prop_liftsemijoin :: Backend c => ([Integer], [Integer]) -> c -> Property
prop_liftsemijoin = makePropEq C.liftsemijoin liftsemijoin
  where
    liftsemijoin (xs, ys) =
        [ [ x | x <- g, x `elem` ys ]
        | g <- groupWith (`mod` 10) xs
        ]

prop_liftantijoin :: Backend c => ([Integer], [Integer]) -> c -> Property
prop_liftantijoin = makePropEq C.liftantijoin liftantijoin
  where
    liftantijoin (xs, ys) =
        [ [ x | x <- g, x `notElem` ys ]
        | g <- groupWith (`mod` 10) xs
        ]

prop_liftthetajoin :: Backend c => ([Integer], [Integer]) -> c -> Property
prop_liftthetajoin = makePropEq C.liftthetajoin liftthetajoin
  where
    liftthetajoin (xs, ys) =
        [ [ (x, y) | x <- g, y <- ys, x < y ]
        | g <- groupWith (`mod` 10) xs
        ]

-----------------------------------------------------------------------
-- HUnit tests for comprehensions

heqjoin_nested1 :: Backend c => c -> Assertion
heqjoin_nested1 = makeEqAssertion "heqjoin_nested" C.eqjoin_nested1 res
  where
    res = [ ((20, ['b']), 20)
          , ((30, ['c', 'd']), 30)
          , ((30, ['c', 'd']), 30)
          , ((40, []), 40)
          ]

hsemijoin :: Backend c => c -> Assertion
hsemijoin = makeEqAssertion "hsemijoin" C.semijoin res
  where
    res = [2, 4, 6, 7]

hsemijoin_range :: Backend c => c -> Assertion
hsemijoin_range = makeEqAssertion "hsemijoin_range" C.semijoin_range res
  where
    res = [2, 4]

hsemijoin_not_null :: Backend c => c -> Assertion
hsemijoin_not_null = makeEqAssertion "hsemijoin_range" C.semijoin_not_null res
  where
    res = [2, 4, 6, 7]

hsemijoin_quant :: Backend c => c -> Assertion
hsemijoin_quant = makeEqAssertion "hsemijoin_quant" C.semijoin_quant res
  where
    res = [6,7]

hantijoin :: Backend c => c -> Assertion
hantijoin = makeEqAssertion "hantijoin" C.antijoin res
  where
    res = [1, 3, 5]

hantijoin_range :: Backend c => c -> Assertion
hantijoin_range = makeEqAssertion "hantijoin_range" C.antijoin_range res
  where
    res = [1, 3, 5, 6, 7]

hantijoin_null :: Backend c => c -> Assertion
hantijoin_null = makeEqAssertion "hantijoin_range" C.antijoin_null res
  where
    res = [1, 3, 5]

hantijoin_class12 :: Backend c => c -> Assertion
hantijoin_class12 = makeEqAssertion "hantijoin_class12" C.antijoin_class12 res
  where
    res = [6,7,8,9,10]

hantijoin_class15 :: Backend c => c -> Assertion
hantijoin_class15 = makeEqAssertion "hantijoin_class15" C.antijoin_class15 res
  where
    res = [5,6,7,8]

hantijoin_class16 :: Backend c => c -> Assertion
hantijoin_class16 = makeEqAssertion "hantijoin_class16" C.antijoin_class16 res
  where
    res = [4,5,6]

hfrontguard :: Backend c => c -> Assertion
hfrontguard = makeEqAssertion "hfrontguard" C.frontguard res
  where
    res = [[],[1,2],[1,2]]

-----------------------------------------------------------------------
-- HUnit tests for nestjoin/nestproduct

njxs1 :: [Integer]
njxs1 = [1,2,3,4,5,6]

njys1 :: [Integer]
njys1 = [3,4,5,6,3,6,4,1,1,1]

hnj1 :: Backend c => c -> Assertion
hnj1 = makeEqAssertion "hnj1" (C.nj1 njxs1 njys1) (nj1 njxs1 njys1)

hnj2 :: Backend c => c -> Assertion
hnj2 = makeEqAssertion "hnj2" (C.nj2 njxs1 njys1) (nj2 njxs1 njys1)

hnj3 :: Backend c => c -> Assertion
hnj3 = makeEqAssertion "hnj3" (C.nj3 njxs1 njys1) (nj3 njxs1 njys1)

hnj4 :: Backend c => c -> Assertion
hnj4 = makeEqAssertion "hnj4" (C.nj4 njxs1 njys1) (nj4 njxs1 njys1)

hnj5 :: Backend c => c -> Assertion
hnj5 = makeEqAssertion "hnj5" (C.nj5 njxs1 njys1) (nj5 njxs1 njys1)

hnj6 :: Backend c => c -> Assertion
hnj6 = makeEqAssertion "hnj6" (C.nj6 njxs1 njys1) (nj6 njxs1 njys1)

hnj7 :: Backend c => c -> Assertion
hnj7 = makeEqAssertion "hnj7" (C.nj7 njxs1 njys1) (nj7 njxs1 njys1)

hnj8 :: Backend c => c -> Assertion
hnj8 = makeEqAssertion "hnj8" (C.nj8 njxs1 njys1) (nj8 njxs1 njys1)

hnj9 :: Backend c => c -> Assertion
hnj9 = makeEqAssertion "hnj9" (C.nj9 njxs1 njys1) (nj9 njxs1 njys1)

hnj10 :: Backend c => c -> Assertion
hnj10 = makeEqAssertion "hnj10" (C.nj10 njxs1 njys1) (nj10 njxs1 njys1)

hnj11 :: Backend c => c -> Assertion
hnj11 = makeEqAssertion "hnj11" (C.nj11 njxs1 njys1) (nj11 njxs1 njys1)

-- Test data for testcase hnj12
njxs2, njys2, njzs2 :: [Integer]
njxs2 = [1,2,3,4,5,5,2]
njys2 = [2,1,0,5,4,4,4]
njzs2 = [6,1,1,3,2,5]

hnj12 :: Backend c => c -> Assertion
hnj12 = makeEqAssertion "hnj12" (C.nj12 njxs2 njys2 njzs2) (nj12 njxs2 njys2 njzs2)

hnp1 :: Backend c => c -> Assertion
hnp1 = makeEqAssertion "hnp1" (C.np1 njxs1 njys1) (np1 njxs1 njys1)

hnp2 :: Backend c => c -> Assertion
hnp2 = makeEqAssertion "hnp2" (C.np2 njxs1 njys1) (np2 njxs1 njys1)

hnp3 :: Backend c => c -> Assertion
hnp3 = makeEqAssertion "hnp3" (C.np3 njxs1 njys1) (np3 njxs1 njys1)

hnp4 :: Backend c => c -> Assertion
hnp4 = makeEqAssertion "hnp4" (C.np4 njxs1 njys1) (np4 njxs1 njys1)

hnjg1 :: Backend c => c -> Assertion
hnjg1 = makeEqAssertion "hnjg1" (C.njg1 njgxs1 njgzs1) (njg1 njgxs1 njgzs1)

hnjg2 :: Backend c => c -> Assertion
hnjg2 = makeEqAssertion "hnjg2" (C.njg2 njgxs1 njgys1) (njg2 njgxs1 njgys1)

hnjg3 :: Backend c => c -> Assertion
hnjg3 = makeEqAssertion "hnjg3" (C.njg3 njgxs1 njgys1 njgzs1) (njg3 njgxs1 njgys1 njgzs1)

hnjg4 :: Backend c => c -> Assertion
hnjg4 = makeEqAssertion "hnjg4" (C.njg4 njgxs1 njgys1 njgzs1) (njg4 njgxs1 njgys1 njgzs1)

hnjg5 :: Backend c => c -> Assertion
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
    [ pair x ([ y | y <- njys, x == y ] ++ ([100, 200, 300]))
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

--------------------------------------------------------------------------------
--

prop_deep_iter :: Backend c => ([Integer], [Integer], [Integer], [Integer], [Integer]) -> c -> Property
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
prop_only_tuple :: Backend c => (Integer, [Integer], [Integer]) -> c -> Property
prop_only_tuple (x, ys, zs) c =
    not (null ys)
    ==>
    makePropEq C.only_tuple only_tuple_native (x, ys, zs) c
  where
    only_tuple_native _ =
        pair x (head [ (y, [ z | z <- zs, x == y ])  | y <- ys ])
