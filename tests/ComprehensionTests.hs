module ComprehensionTests where

import           Common
import qualified DSHComprehensions                    as C

import           Test.Framework                       (Test, testGroup)
import           Test.Framework.Providers.HUnit
import           Test.Framework.Providers.QuickCheck2 (testProperty)
import           Test.HUnit                           (Assertion)
import           Test.QuickCheck

tests_comprehensions :: Test
tests_comprehensions = testGroup "Comprehensions"
    [ testProperty "cartprod" prop_cartprod
    , testProperty "eqjoin" prop_eqjoin
    , testProperty "eqjoinproj" prop_eqjoinproj
    , testProperty "eqjoinpred" prop_eqjoinpred
    , testProperty "eqjointuples" prop_eqjointuples
    , testProperty "thetajoin_eq" prop_thetajoin_eq
    , testProperty "thetajoin_neq" prop_thetajoin_neq
    , testProperty "eqjoin3" prop_eqjoin3
    , testProperty "eqjoin_nested_left" prop_eqjoin_nested_left
    , testProperty "eqjoin_nested_right" prop_eqjoin_nested_right
    , testProperty "eqjoin_nested_both" prop_eqjoin_nested_both
    , testProperty "nestjoin" prop_nestjoin
    , testProperty "antijoin class12" prop_aj_class12
    , testProperty "antijoin class15" prop_aj_class15
    , testProperty "antijoin class16" prop_aj_class16
    ]

tests_join_hunit :: Test
tests_join_hunit = testGroup "HUnit joins"
    [ testCase "heqjoin_nested1" heqjoin_nested1
    , testCase "hsemijoin" hsemijoin
    , testCase "hsemijoin_range" hsemijoin_range
    , testCase "hsemijoin_quant" hsemijoin_quant
    , testCase "hsemijoin_not_null" hsemijoin_not_null
    , testCase "hantijoin" hantijoin
    , testCase "hantijoin_range" hantijoin_range
    , testCase "hantijoin_null" hantijoin_null
    , testCase "hantijoin_class12" hantijoin_class12
    , testCase "hantijoin_class15" hantijoin_class15
    , testCase "hantijoin_class16" hantijoin_class16
    ]

tests_nest_head_hunit :: Test
tests_nest_head_hunit = testGroup "HUnit head nesting"
    [ testCase "hnj1" hnj1
    , testCase "hnj2" hnj2
    , testCase "hnj3" hnj3
    , testCase "hnj4" hnj4
    , testCase "hnj5" hnj5
    , testCase "hnj6" hnj6
    , testCase "hnj7" hnj7
    , testCase "hnj8" hnj8
    , testCase "hnj9" hnj9
    , testCase "hnj10" hnj10
    , testCase "hnj11" hnj11
    , testCase "hnp1" hnp1
    , testCase "hnp2" hnp2
    , testCase "hnp3" hnp3
    , testCase "hnp4" hnp4
    ]

tests_nest_guard_hunit :: Test
tests_nest_guard_hunit = testGroup "HUnit guard nesting"
    [ testCase "hnjg1" hnjg1
    , testCase "hnjg2" hnjg2
    , testCase "hnjg3" hnjg3
    , testCase "hnjg4" hnjg4
    , testCase "hnjg5" hnjg5
    ]

---------------------------------------------------------------------------------
-- QuickCheck properties for comprehensions

prop_cartprod :: ([Integer], [Integer]) -> Property
prop_cartprod = makeProp C.cartprod cartprod_native
  where
    cartprod_native (xs, ys) = [ (x, y) | x <- xs, y <- ys]

prop_eqjoin :: ([Integer], [Integer]) -> Property
prop_eqjoin = makeProp C.eqjoin eqjoin_native
  where
    eqjoin_native (xs, ys) = [ (x, y) | x <- xs , y <- ys , x == y ]

prop_eqjoinproj :: ([Integer], [Integer]) -> Property
prop_eqjoinproj = makeProp C.eqjoinproj eqjoinproj_native
  where
    eqjoinproj_native (xs, ys) = [ (x, y) | x <- xs , y <- ys , (2 * x) == y ]

prop_eqjoinpred :: (Integer, [Integer], [Integer]) -> Property
prop_eqjoinpred = makeProp C.eqjoinpred eqjoinpred_native
  where
    eqjoinpred_native (x', xs, ys) = [ (x, y) | x <- xs , y <- ys , x == y , x > x']

prop_eqjointuples :: ([(Integer, Integer)], [(Integer, Integer)]) -> Property
prop_eqjointuples = makeProp C.eqjointuples eqjointuples_native
  where
    eqjointuples_native (xs, ys) = [ (x1 * x2, y1, y2)
                                   | (x1, x2) <- xs
                                   , (y1, y2) <- ys
                                   , x1 == y2
                                   ]

prop_thetajoin_eq :: ([(Integer, Integer)], [(Integer, Integer)]) -> Property
prop_thetajoin_eq = makeProp C.thetajoin_eq thetajoin_eq_native
  where
    thetajoin_eq_native (xs, ys) = [ (x1 * x2, y1, y2)
                                   | (x1, x2) <- xs
                                   , (y1, y2) <- ys
                                   , x1 == y2
                                   , y1 == x2
                                   ]

prop_thetajoin_neq :: ([(Integer, Integer)], [(Integer, Integer)]) -> Property
prop_thetajoin_neq = makeProp C.thetajoin_neq thetajoin_neq_native
  where
    thetajoin_neq_native (xs, ys) = [ (x1 * x2, y1, y2)
                                    | (x1, x2) <- xs
                                    , (y1, y2) <- ys
                                    , x1 == y2
                                    , y1 /= x2
                                    ]


prop_eqjoin3 :: ([Integer], [Integer], [Integer]) -> Property
prop_eqjoin3 = makeProp C.eqjoin3 eqjoin3_native
  where
    eqjoin3_native (xs, ys, zs) = [ (x, y, z) | x <- xs , y <- ys , z <- zs , x == y , y == z]

prop_eqjoin_nested_left :: ([(Integer, [Integer])], [Integer]) -> Property
prop_eqjoin_nested_left = makeProp C.eqjoin_nested_left eqjoin_nested_left_native
  where
    eqjoin_nested_left_native (xs, ys) = [ (x, y) | x <- xs , y <- ys , fst x == y]

prop_eqjoin_nested_right :: ([Integer], [(Integer, [Integer])]) -> Property
prop_eqjoin_nested_right = makeProp C.eqjoin_nested_right eqjoin_nested_right_native
  where
    eqjoin_nested_right_native (xs, ys) = [ (x, y) | x <- xs , y <- ys , x == fst y]

prop_eqjoin_nested_both :: ([(Integer, [Integer])], [(Integer, [Integer])]) -> Property
prop_eqjoin_nested_both = makeProp C.eqjoin_nested_both eqjoin_nested_both_native
  where
    eqjoin_nested_both_native (xs, ys) = [ (x, y) | x <- xs , y <- ys , fst x == fst y]

prop_nestjoin :: ([Integer], [Integer]) -> Property
prop_nestjoin = makeProp C.nestjoin nestjoin_native
  where
    nestjoin_native (xs, ys) = [ (x, [ y | y <- ys, x == y ]) | x <- xs]

prop_aj_class12 :: ([Integer], [Integer]) -> Property
prop_aj_class12 = makeProp C.aj_class12 aj_class12_native
  where
    aj_class12_native (ajxs, ajys) = [ x 
                                     | x <- ajxs
                                     , and [ x == y | y <- ajys, y > 10 ]
                                     ]

prop_aj_class15 :: ([Integer], [Integer]) -> Property
prop_aj_class15 = makeProp C.aj_class15 aj_class15_native
  where
    aj_class15_native (ajxs, ajys) = [ x 
                                     | x <- ajxs
                                     , and [ y `mod` 4 == 0 | y <- ajys, x < y ]
                                     ]

prop_aj_class16 :: ([Integer], [Integer]) -> Property
prop_aj_class16 = makeProp C.aj_class16 aj_class16_native
  where
    aj_class16_native (ajxs, ajys) = [ x 
                                     | x <- ajxs
                                     , and [ y <= 2 * x | y <- ajys, x < y ]
                                     ]

-----------------------------------------------------------------------
-- HUnit tests for comprehensions

heqjoin_nested1 :: Assertion
heqjoin_nested1 = makeEqAssertion "heqjoin_nested" C.eqjoin_nested1 res
  where
    res = [ ((20, ['b']), 20)
          , ((30, ['c', 'd']), 30)
          , ((30, ['c', 'd']), 30)
          , ((40, []), 40)
          ]

hsemijoin :: Assertion
hsemijoin = makeEqAssertion "hsemijoin" C.semijoin res
  where
    res = [2, 4, 6, 7]

hsemijoin_range :: Assertion
hsemijoin_range = makeEqAssertion "hsemijoin_range" C.semijoin_range res
  where
    res = [2, 4]

hsemijoin_not_null :: Assertion
hsemijoin_not_null = makeEqAssertion "hsemijoin_range" C.semijoin_not_null res
  where
    res = [2, 4, 6, 7]

hsemijoin_quant :: Assertion
hsemijoin_quant = makeEqAssertion "hsemijoin_quant" C.semijoin_quant res
  where
    res = [6,7]

hantijoin :: Assertion
hantijoin = makeEqAssertion "hantijoin" C.antijoin res
  where
    res = [1, 3, 5]

hantijoin_range :: Assertion
hantijoin_range = makeEqAssertion "hantijoin_range" C.antijoin_range res
  where
    res = [1, 3]

hantijoin_not_null :: Assertion
hantijoin_not_null = makeEqAssertion "hantijoin_range" C.antijoin_null res
  where
    res = [1, 3, 5]

hantijoin_class12 :: Assertion
hantijoin_class12 = makeEqAssertion "hantijoin_class12" C.antijoin_class12 res
  where
    res = [6,7,8,9,10]

hantijoin_class15 :: Assertion
hantijoin_class15 = makeEqAssertion "hantijoin_class15" C.antijoin_class15 res
  where
    res = [5,6,7,8]

hantijoin_class16 :: Assertion
hantijoin_class16 = makeEqAssertion "hantijoin_class16" C.antijoin_class16 res
  where
    res = [4,5,6]

-----------------------------------------------------------------------
-- HUnit tests for nestjoin/nestproduct

njxs1 :: [Integer]
njxs1 = [1,2,3,4,5,6]

njys1 :: [Integer]
njys1 = [3,4,5,6,3,6,4,1,1,1]

hnj1 :: Assertion
hnj1 = makeEqAssertion "hnj1" (C.nj1 njxs1 njys1) (nj1 njxs1 njys1)

hnj2 :: Assertion
hnj2 = makeEqAssertion "hnj2" (C.nj2 njxs1 njys1) (nj2 njxs1 njys1)

hnj3 :: Assertion
hnj3 = makeEqAssertion "hnj3" (C.nj3 njxs1 njys1) (nj3 njxs1 njys1)

hnj4 :: Assertion
hnj4 = makeEqAssertion "hnj4" (C.nj4 njxs1 njys1) (nj4 njxs1 njys1)

hnj5 :: Assertion
hnj5 = makeEqAssertion "hnj5" (C.nj5 njxs1 njys1) (nj5 njxs1 njys1)

hnj6 :: Assertion
hnj6 = makeEqAssertion "hnj6" (C.nj6 njxs1 njys1) (nj6 njxs1 njys1)

hnj7 :: Assertion
hnj7 = makeEqAssertion "hnj7" (C.nj7 njxs1 njys1) (nj7 njxs1 njys1)

hnj8 :: Assertion
hnj8 = makeEqAssertion "hnj8" (C.nj8 njxs1 njys1) (nj8 njxs1 njys1)

hnj9 :: Assertion
hnj9 = makeEqAssertion "hnj9" (C.nj9 njxs1 njys1) (nj9 njxs1 njys1)

hnj10 :: Assertion
hnj10 = makeEqAssertion "hnj10" (C.nj10 njxs1 njys1) (nj10 njxs1 njys1)

hnj11 :: Assertion
hnj11 = makeEqAssertion "hnj11" (C.nj11 njxs1 njys1) (nj11 njxs1 njys1)

hnp1 :: Assertion
hnp1 = makeEqAssertion "hnp1" (C.np1 njxs1 njys1) (np1 njxs1 njys1)

hnp2 :: Assertion
hnp2 = makeEqAssertion "hnp2" (C.np2 njxs1 njys1) (np2 njxs1 njys1)

hnp3 :: Assertion
hnp3 = makeEqAssertion "hnp3" (C.np3 njxs1 njys1) (np3 njxs1 njys1)

hnp4 :: Assertion
hnp4 = makeEqAssertion "hnp4" (C.np4 njxs1 njys1) (np4 njxs1 njys1)

hnjg1 :: Assertion
hnjg1 = makeEqAssertion "hnjg1" (C.njg1 njgxs1 njgzs1) (njg1 njgxs1 njgzs1)

hnjg2 :: Assertion
hnjg2 = makeEqAssertion "hnjg2" (C.njg2 njgxs1 njgys1) (njg2 njgxs1 njgys1)

hnjg3 :: Assertion
hnjg3 = makeEqAssertion "hnjg3" (C.njg3 njgxs1 njgys1 njgzs1) (njg3 njgxs1 njgys1 njgzs1)

hnjg4 :: Assertion
hnjg4 = makeEqAssertion "hnjg4" (C.njg4 njgxs1 njgys1 njgzs1) (njg4 njgxs1 njgys1 njgzs1)

hnjg5 :: Assertion
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
