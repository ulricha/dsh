module ComprehensionTests where

import           Common
import           DSHComprehensions

import           Test.QuickCheck
import           Test.HUnit(Assertion)
import           Test.Framework (Test, testGroup)
import           Test.Framework.Providers.QuickCheck2 (testProperty)
import           Test.Framework.Providers.HUnit

tests_comprehensions :: Test
tests_comprehensions = testGroup "Comprehensions"
    [ testProperty "eqjoin" prop_eqjoin
    , testProperty "eqjoinproj" prop_eqjoinproj
    , testProperty "eqjoinpred" prop_eqjoinpred
    , testProperty "eqjoin3" prop_eqjoin3
    , testProperty "eqjoin_nested" prop_eqjoin_nested
    , testProperty "nestjoin" prop_nestjoin
    ]
    

tests_join_hunit :: Test
tests_join_hunit = testGroup "HUnit joins"
    [ testCase "heqjoin_nested1" heqjoin_nested1
    , testCase "hsemijoin" hsemijoin
    ]

---------------------------------------------------------------------------------
-- QuickCheck properties for comprehensions

prop_eqjoin :: ([Integer], [Integer]) -> Property
prop_eqjoin = makeProp eqjoin 
                       (\(xs, ys) -> [ (x, y) | x <- xs , y <- ys , x == y ])

prop_eqjoinproj :: ([Integer], [Integer]) -> Property
prop_eqjoinproj = 
  makeProp eqjoinproj (\(xs, ys) -> [ (x, y) | x <- xs , y <- ys , (2 * x) == y ])
  
prop_eqjoinpred :: (Integer, [Integer], [Integer]) -> Property
prop_eqjoinpred =
  makeProp eqjoinpred
           (\(x', xs, ys) ->
             [ (x, y)
             | x <- xs
             , y <- ys
             , x == y
             , x > x'
             ])

prop_eqjoin3 :: ([Integer], [Integer], [Integer]) -> Property
prop_eqjoin3 =
  makeProp eqjoin3
           (\(xs, ys, zs) ->
             [ (x, y, z)
             | x <- xs
             , y <- ys
             , z <- zs
             , x == y
             , y == z
             ])
             
prop_eqjoin_nested :: ([(Integer, [Integer])], [Integer]) -> Property
prop_eqjoin_nested =
  makeProp eqjoin_nested
           (\(xs, ys) ->
             [ (x, y)
             | x <- xs
             , y <- ys
             , fst x == y
             ])

prop_nestjoin :: ([Integer], [Integer]) -> Property
prop_nestjoin =
  makeProp nestjoin
           (\(xs, ys) ->
             [ (x, [ y | y <- ys, x == y ])
             | x <- xs
             ])

-----------------------------------------------------------------------
-- HUnit tests for comprehensions

heqjoin_nested1 :: Assertion
heqjoin_nested1 = makeEqAssertion "heqjoin_nested" eqjoin_nested1 res
  where
    res = [ ((20, ['b']), 20)
          , ((30, ['c', 'd']), 30)
          , ((30, ['c', 'd']), 30)
          , ((40, []), 40)
          ]

hsemijoin :: Assertion
hsemijoin = makeEqAssertion "hsemijoin" semijoin res
  where 
    res = [2, 4, 6]
    
  
