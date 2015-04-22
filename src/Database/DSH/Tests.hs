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
runTests :: Backend c => c -> [c -> Test] -> IO ()
runTests conn tests = do
    args <- getArgs
    let args' = if or $ map (L.isPrefixOf "-s") args
                then args
                else "-s5":args
    defaultMainWithArgs (map (\t -> t conn) tests) args'

-- | All available tests in one package.
defaultTests :: Backend c => [c -> Test]
defaultTests =
    [ tests_types
    , tests_tuples
    , tests_join_hunit
    , tests_nest_head_hunit
    , tests_nest_guard_hunit
    , tests_combinators_hunit
    , tests_comprehensions
    , tests_lifted_joins
    , tests_boolean
    , tests_numerics
    , tests_maybe
    , tests_either
    , tests_lists
    , tests_lifted
    , tests_laws
    ]
