module Database.DSH.Tests.LawTests
    ( tests_laws
    ) where



import           Test.Framework            (Test, testGroup)
import           Test.QuickCheck
import           Test.QuickCheck.Monadic

import qualified Database.DSH              as Q
import           Database.DSH.Backend
import           Database.DSH.Compiler
import           Database.DSH.Tests.Common

tests_laws :: Backend c => c -> Test
tests_laws conn = testGroup "List Laws"
    [ testPropertyConn conn "takedrop" prop_takedrop
    , testPropertyConn conn "reverse id" prop_reverse_identity
    , testPropertyConn conn "reverse sort" prop_reverse_sort
    , testPropertyConn conn "reverse sort tuple" prop_reverse_sort_tuple
    ]

--------------------------------------------------------------------------------
-- Common list laws

prop_takedrop :: Backend c => (Integer, [Integer]) -> c -> Property
prop_takedrop (i, xs) conn = monadicIO $ do
    let q = Q.take (Q.toQ i) (Q.toQ xs) Q.++ Q.drop (Q.toQ i) (Q.toQ xs)
    res <- run $ runQ conn q
    assert $ res == xs

prop_reverse_identity :: Backend c => [Integer] -> c -> Property
prop_reverse_identity xs conn = monadicIO $ do
    let q = Q.reverse $ Q.reverse (Q.toQ xs)
    res <- run $ runQ conn q
    assert $ res == xs

prop_reverse_sort :: Backend c => OrderedList Integer -> c -> Property
prop_reverse_sort (Ordered xs) conn = monadicIO $ do
    let q = Q.sortWith id $ Q.reverse (Q.toQ xs)
    res <- run $ runQ conn q
    assert $ res == xs

prop_reverse_sort_tuple :: Backend c => OrderedList (Integer, Integer) -> c -> Property
prop_reverse_sort_tuple (Ordered xs) conn = monadicIO $ do
    let q = Q.sortWith id $ Q.reverse (Q.toQ xs)
    res <- run $ runQ conn q
    assert $ res == xs
