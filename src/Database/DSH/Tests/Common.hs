{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- | Helpers for the construction of DSH test cases.
module Database.DSH.Tests.Common
    ( makePropEq
    , makePropDouble
    , makePropDoubles
    , makeEqAssertion
    , testPropertyConn
    , uncurryQ
    , filterNullChar
    ) where

import qualified Data.Text                            as T
import qualified Data.Time.Calendar                   as C
import qualified Data.Decimal                         as D

import           Test.Framework
import           Test.Framework.Providers.QuickCheck2
import           Test.HUnit                           (Assertion, assertEqual)
import           Test.QuickCheck
import           Test.QuickCheck.Monadic


import qualified Database.DSH                         as Q
import           Database.DSH.Backend
import           Database.DSH.Compiler

instance Arbitrary T.Text where
  arbitrary = fmap T.pack arbitrary

instance Arbitrary C.Day where
  arbitrary = C.ModifiedJulianDay <$> choose (25000, 80000)

instance Arbitrary D.Decimal where
  arbitrary = D.Decimal <$> choose (1,8) <*> choose (1,10^(6 :: Int))

uncurryQ :: (Q.QA a, Q.QA b) => (Q.Q a -> Q.Q b -> Q.Q c) -> Q.Q (a,b) -> Q.Q c
uncurryQ f = uncurry f . Q.view

filterNullChar :: T.Text -> T.Text
filterNullChar = T.filter (/= '\0')

eps :: Double
eps = 1.0E-3

close :: Double -> Double -> Bool
close a b = abs (a - b) < eps

-- | A simple property that should hold for a DSH query: Given any
-- input, its result should be the same as the corresponding native
-- Haskell code. 'The same' is defined by a predicate.
makeProp :: (Q.QA a, Q.QA b, Show a, Show b, Backend c)
         => (b -> b -> Bool)
         -> (Q.Q a -> Q.Q b)
         -> (a -> b)
         -> a
         -> c
         -> Property
makeProp eq f1 f2 arg conn = monadicIO $ do
    db <- run $ runQ conn $ f1 (Q.toQ arg)
    let hs = f2 arg
    assert $ db `eq` hs

-- | Compare query result and native result by equality.
makePropEq :: (Eq b, Q.QA a, Q.QA b, Show a, Show b, Backend c)
           => (Q.Q a -> Q.Q b)
           -> (a -> b)
           -> a
           -> c
           -> Property
makePropEq = makeProp (==)

-- | Compare the double query result and native result.
makePropDouble :: (Q.QA a, Show a, Backend c)
               => (Q.Q a -> Q.Q Double)
               -> (a -> Double)
               -> a
               -> c
               -> Property
makePropDouble = makeProp close

makePropDoubles :: (Q.QA a, Show a, Backend c)
                => (Q.Q a -> Q.Q [Double])
                -> (a -> [Double])
                -> a
                -> c
                -> Property
makePropDoubles = makeProp deltaList
  where
    deltaList as bs = and $ zipWith close as bs

-- | Equality HUnit assertion
makeEqAssertion :: (Show a, Eq a, Q.QA a, Backend c)
                => String
                -> Q.Q a
                -> a
                -> c
                -> Assertion
makeEqAssertion msg q expRes conn = do
    actualRes <- runQ conn q
    assertEqual msg expRes actualRes

testPropertyConn :: (Show a, Arbitrary a, Backend c)
                 => c -> TestName -> (a -> c -> Property) -> Test
testPropertyConn conn name t = testProperty name (\a -> t a conn)
