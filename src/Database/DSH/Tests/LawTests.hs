module Database.DSH.Tests.LawTests
    ( tests_laws
    ) where

import           Test.Framework                       (Test, testGroup)

import           Test.QuickCheck
import           Test.QuickCheck.Monadic

import qualified Database.DSH                         as Q
import           Database.DSH.Backend
import           Database.DSH.Compiler
import           Database.DSH.Tests.Common

tests_laws :: Backend c => c -> Test
tests_laws conn = testGroup "List Laws"
    [ testPropertyConn conn "takedrop" prop_takedrop
    , testPropertyConn conn "reverse_id" prop_reverse_identity
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
