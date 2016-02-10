{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE MonadComprehensions #-}

module Database.DSH.Common.Sequence
    ( transposeSeq
    ) where

import qualified Data.Sequence as S
import Data.Sequence(ViewL(..), viewl, (<|))

-- | Transpose a two-dimensional sequence. This function behaves in the same way
-- as 'Data.List.transpose'.
transposeSeq :: S.Seq (S.Seq a) -> S.Seq (S.Seq a)
transposeSeq (viewl -> EmptyL) = S.empty
transposeSeq (viewl -> (viewl -> EmptyL) :< xss) = transposeSeq xss
transposeSeq (viewl -> (viewl -> x :< xs) :< xss) =
    (x <| [ h | (viewl -> h :< _) <- xss ])
    <|
    transposeSeq (xs <| [ t | (viewl -> _ :< t) <- xss ])
