module Database.DSH.Tests
    ( defaultTests
    , runTests
    , module Database.DSH.Tests.ComprehensionTests
    , module Database.DSH.Tests.CombinatorTests
    ) where

import           Test.Framework

import           Database.DSH.Backend
import           Database.DSH.Tests.CombinatorTests
import           Database.DSH.Tests.ComprehensionTests

-- | Convenience function for running tests
runTests :: Backend c => c -> [c -> Test] -> IO ()
runTests conn tests = defaultMain $ map (\t -> t conn) tests

-- | All available tests in one package.
defaultTests :: Backend c => c -> [Test]
defaultTests conn =
    [ tests_types conn
    , tests_tuples conn
    , tests_join_hunit conn
    , tests_nest_head_hunit conn
    , tests_nest_guard_hunit conn
    , tests_combinators_hunit conn
    , tests_comprehensions conn
    , tests_boolean conn
    , tests_numerics conn
    , tests_maybe conn
    , tests_either conn
    , tests_lists conn
    , tests_lifted conn
    ]
