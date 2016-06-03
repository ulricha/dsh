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
import           Database.DSH.Compiler
import           Database.DSH.Tests.CombinatorTests
import           Database.DSH.Tests.ComprehensionTests
import           Database.DSH.Tests.LawTests
import           Database.DSH.Tests.Common

-- | Convenience function for running tests
runTests :: [String] -> TestTree -> IO ()
runTests args tests = withArgs args (defaultMain tests)

-- | All available tests in one package.
defaultTests :: forall v b.(Backend b, VectorLang v) => DSHTestTree v b
defaultTests codeGen conn = testGroup "default_tests" $ map (\g -> g codeGen conn) testGroups
  where
    testGroups :: [DSHTestTree v b]
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
