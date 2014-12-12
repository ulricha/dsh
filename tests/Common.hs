module Common where

import qualified Database.DSH as Q
import           Database.DSH (Q, QA)

#ifdef TESTSQL
import           Database.DSH.Compiler (runQ)
#endif

#ifdef TESTSQL
import qualified Database.HDBC as HDBC
import           Database.HDBC.PostgreSQL
#endif

import           Test.HUnit(assertEqual, Assertion)
import           Test.QuickCheck
import           Test.QuickCheck.Monadic

import           Data.Text (Text)
import qualified Data.Text as Text

#ifdef TESTSQL
getConn :: IO Connection
getConn = connectPostgreSQL "user = 'au' password = 'foobar' host = 'localhost' dbname = 'test'"
#endif

-------------------------------------------------------------------------------
-- Make QuickCheck properties

instance Arbitrary Text where
  arbitrary = fmap Text.pack arbitrary

makeProp :: (Eq b, QA a, QA b, Show a, Show b)
            => (Q a -> Q b)
            -> (a -> b)
            -> a
            -> Property
makeProp f1 f2 arg = monadicIO $ do
#ifdef TESTSQL
    c  <- run $ getConn
    db <- run $ runQ c $ f1 (Q.toQ arg)
    run $ HDBC.disconnect c
#endif
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
#ifdef TESTSQL
    c  <- run $ getConn
    db <- run $ runQ c $ f1 (Q.toQ arg)
    run $ HDBC.disconnect c
#endif
    let hs = f2 arg
    let eps = 1.0E-3 :: Double;
    assert (abs (db - hs) < eps)

makePropListDouble :: (QA a, Show a)
                  => (Q a -> Q [Double])
                  -> (a -> [Double])
                  -> a
                  -> Property
makePropListDouble f1 f2 arg = monadicIO $ do
#ifdef TESTSQL
    c  <- run $ getConn
    db <- run $ runQ c $ f1 (Q.toQ arg)
    run $ HDBC.disconnect c
#endif
    let hs = f2 arg
    let eps = 1.0E-3 :: Double;
    assert $ and [abs (d - h) < eps | (d, h) <- zip db hs]

uncurryQ :: (QA a, QA b) => (Q a -> Q b -> Q c) -> Q (a,b) -> Q c
uncurryQ f = uncurry f . Q.view

-------------------------------------------------------------------------------
-- Make HUnit assertion

-- | Equality HUnit assertion
makeEqAssertion :: (Show a, Eq a, QA a) => String -> Q.Q a -> a -> Assertion
makeEqAssertion msg q r = do
#ifdef TESTSQL
    c  <- getConn
    r' <- runQ c q
    HDBC.disconnect c
#endif
    assertEqual msg r r'
    
