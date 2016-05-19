{-# LANGUAGE ScopedTypeVariables #-}

-- | Generic DSH test queries that can be run by any backend for
-- concrete testing.
module Database.DSH.Tests
    ( defaultTests
    , runTests
    , module Database.DSH.Tests.ComprehensionTests
    , module Database.DSH.Tests.CombinatorTests
    ) where

import           System.Environment
import           Test.Tasty

import           Database.DSH.Backend
import           Database.DSH.Tests.CombinatorTests
import           Database.DSH.Tests.ComprehensionTests
import           Database.DSH.Tests.LawTests

-- | Convenience function for running tests
runTests :: [String] -> TestTree -> IO ()
runTests args tests = withArgs args (defaultMain tests)

-- | All available tests in one package.
defaultTests :: forall c.Backend c => c -> TestTree
defaultTests conn = testGroup "default_tests" $ map ($ conn) testGroups
  where
    testGroups :: [c -> TestTree]
    testGroups =
        [ typeTests
        , tupleTests
        , tests_join_hunit
        , tests_nest_head_hunit
        , tests_nest_guard_hunit
        , hunitCombinatorTests
        , tests_comprehensions
        , tests_lifted_joins
        , booleanTests
        , numericTests
        , maybeTests
        , eitherTests
        , listTests
        , liftedTests
        , distTests
        , tests_laws
        , otherTests
        ]
