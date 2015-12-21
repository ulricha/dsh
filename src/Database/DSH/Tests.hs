-- | Generic DSH test queries that can be run by any backend for
-- concrete testing.
module Database.DSH.Tests
    ( defaultTests
    , runTests
    , module Database.DSH.Tests.ComprehensionTests
    , module Database.DSH.Tests.CombinatorTests
    ) where

import qualified Data.List                             as L
import           System.Environment

import           Test.Framework

import           Database.DSH.Backend
import           Database.DSH.Tests.CombinatorTests
import           Database.DSH.Tests.ComprehensionTests
import           Database.DSH.Tests.LawTests

-- | Convenience function for running tests
runTests :: Backend c => [String] -> c -> [c -> Test] -> IO ()
runTests args conn tests = defaultMainWithArgs (map (\t -> t conn) tests) args

-- | All available tests in one package.
defaultTests :: Backend c => [c -> Test]
defaultTests =
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
    , tests_laws
    ]
