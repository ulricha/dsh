{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- | Helpers for the construction of DSH test cases.
module Database.DSH.Tests.Common
    ( DSHProperty
    , DSHAssertion
    , DSHTestTree
    , makePropEq
    , makePropDouble
    , makePropDoubles
    , makeEqAssertion
    , testPropertyConn
    , uncurryQ
    , filterNullChar
    ) where

import qualified Data.Decimal            as D
import qualified Data.Text               as T
import qualified Data.Time.Calendar      as C

import           Test.HUnit              (Assertion, assertEqual)
import           Test.QuickCheck
import           Test.QuickCheck.Monadic
import           Test.Tasty
import           Test.Tasty.QuickCheck

import qualified Database.DSH            as Q
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

type DSHProperty v b = BackendCodeGen v b -> BackendConn b -> Property
type DSHAssertion v b = BackendCodeGen v b -> BackendConn b -> Assertion
type DSHTestTree v b = BackendCodeGen v b -> BackendConn b -> TestTree

-- | A simple property that should hold for a DSH query: Given any
-- input, its result should be the same as the corresponding native
-- Haskell code. 'The same' is defined by a predicate.
makeProp :: (Q.QA a, Q.QA c, Show a, Show c, Backend b, VectorLang v)
         => (c -> c -> Bool)
         -> (Q.Q a -> Q.Q c)
         -> (a -> c)
         -> a
         -> DSHProperty v b
makeProp eq f1 f2 arg codeGen conn = monadicIO $ do
    db <- run $ runQ codeGen conn $ f1 (Q.toQ arg)
    let hs = f2 arg
    assert $ db `eq` hs

-- | Compare query result and native result by equality.
makePropEq :: (Eq c, Q.QA a, Q.QA c, Show a, Show c, Backend b, VectorLang v)
           => (Q.Q a -> Q.Q c)
           -> (a -> c)
           -> a
           -> DSHProperty v b
makePropEq = makeProp (==)

-- | Compare the double query result and native result.
makePropDouble :: (Q.QA a, Show a, Backend b, VectorLang v)
               => (Q.Q a -> Q.Q Double)
               -> (a -> Double)
               -> a
               -> DSHProperty v b
makePropDouble = makeProp close

makePropDoubles :: (Q.QA a, Show a, Backend b, VectorLang v)
                => (Q.Q a -> Q.Q [Double])
                -> (a -> [Double])
                -> a
                -> DSHProperty v b
makePropDoubles = makeProp deltaList
  where
    deltaList as bs = and $ zipWith close as bs

-- | Equality HUnit assertion
makeEqAssertion :: (Show a, Eq a, Q.QA a, Backend b, VectorLang v)
                => String
                -> Q.Q a
                -> a
                -> DSHAssertion v b
makeEqAssertion msg q expRes codeGen conn = do
    actualRes <- runQ codeGen conn q
    assertEqual msg expRes actualRes

testPropertyConn :: (Show a, Arbitrary a, Backend b, VectorLang v)
                 => BackendCodeGen v b
                 -> BackendConn b
                 -> TestName
                 -> (a -> BackendCodeGen v b -> BackendConn b -> Property)
                 -> TestTree
testPropertyConn codeGen conn name t = testProperty name (\a -> t a codeGen conn)
