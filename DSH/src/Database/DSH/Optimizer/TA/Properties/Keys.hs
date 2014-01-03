-- FIXME once 7.8 is out, use overloaded list notation for sets
-- instead of S.fromList!
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE TemplateHaskell     #-}

module Database.DSH.Optimizer.TA.Properties.Keys where

import Debug.Trace
import Text.Printf

import Data.List
import qualified Data.Set.Monad as S

import           Database.DSH.Impossible

import           Database.Algebra.Pathfinder.Data.Algebra

import           Database.DSH.Optimizer.TA.Properties.Aux
import           Database.DSH.Optimizer.TA.Properties.Types
                 
subsetsOfSize :: Ord a => Int -> S.Set a -> S.Set (S.Set a)
subsetsOfSize n s
    | n == 0                    = S.singleton S.empty
    | S.size s < n || n < 0     = error "onlyLists: out of range n"
    | S.size s == n             = S.singleton s
    | otherwise                 = S.fromDistinctAscList . map S.fromDistinctAscList $
                                                         go n (S.size s) (S.toList s)
      where
        go 1 _ xs = map return xs
        go k l (x:xs)
            | k == l = [x:xs]
            | otherwise = map (x:) (go (k-1) (l-1) xs) ++ go k (l-1) xs

mapCol :: Proj -> S.Set (AttrName, AttrName)
mapCol (a, ColE b) = S.singleton (a, b)
mapCol _           = S.empty

-- | Enumerate all subsets of size n

-- | Compute keys for rank and rowrank operators
rowRankKeys :: AttrName -> S.Set AttrName -> Card1 -> S.Set PKey -> S.Set PKey
rowRankKeys resCol sortCols childCard1 childKeys =
    -- All old keys stay intact
    childKeys
    ∪
    -- Trivial case: singleton input
    [ ss resCol | childCard1 ]
    ∪
    -- If sorting columns form a part of a key, the output column
    -- combined with the key columns that are not sorting columns also
    -- is a key.
    [ (ss resCol) ∪ (k ∖ sortCols)
    | k <- childKeys
    , k ∩ sortCols /= S.empty
    ]

inferKeysNullOp :: NullOp -> S.Set PKey
inferKeysNullOp op =
    case op of
        -- FIXME check all combinations of columns for uniqueness
        LitTable vals schema  -> S.fromList
                                 $ map (ss . snd) 
                                 $ filter (isUnique . fst)
                                 $ zip (transpose vals) (map fst schema)
          where
            isUnique :: [AVal] -> Bool
            isUnique vs = (length $ nub vs) == (length vs)

        EmptyTable _          -> S.empty
        TableRef (_, _, keys) -> S.fromList $ map (\(Key k) -> ls k) keys

inferKeysUnOp :: S.Set PKey -> Card1 -> S.Set AttrName -> UnOp -> S.Set PKey
inferKeysUnOp childKeys childCard1 childCols op =
    case op of
        RowNum (resCol, _, Nothing)    -> S.insert (ss resCol) childKeys
        RowNum (resCol, _, Just pattr) -> (S.singleton $ ls [resCol, pattr])
                                          ∪
                                          [ ss resCol | childCard1 ]
                                          ∪
                                          childKeys
        RowRank (resCol, sortInfo)     -> rowRankKeys resCol (ls $ map fst sortInfo) childCard1 childKeys
        Rank (resCol, sortInfo)        -> rowRankKeys resCol (ls $ map fst sortInfo) childCard1 childKeys

        -- This is just the standard Pathfinder way: we take all keys
        -- whose columns survive the projection and update to the new
        -- attr names. We could consider all expressions, but need to
        -- be careful here as not all operators might be injective.
        Project projs           -> -- all sets A of a's s.t. |A| = |k| and 
                                   -- associated bs = k
                                   S.foldr S.union S.empty
                                   [ [ as
                                     | as <- subsetsOfSize (S.size k) pa
                                     , let bs = [ b | (a, b) <- attrPairs, a ∈ as ]
                                     , bs == k
                                     ]
                                   | k <- childKeys
                                   -- check that the key survives at all
                                   , let attrPairs = S.unions $ map mapCol projs
                                   , k ⊆ [ snd x | x <- attrPairs ]
                                   -- generate the set pa of a's s.t. (a, b) ∈ attrPairs and b ∈ k
                                   -- i.e. consider only those a's for which the original b is
                                   -- actually part of the current key.
                                   , let pa = [ a | (a, b) <- attrPairs, b ∈ k ]
                                   ]

        Select _                -> childKeys
        Distinct _              -> S.insert childCols childKeys 
        Aggr (_, [])            -> S.empty
        Aggr (_, pcols@(_ : _)) -> S.singleton $ S.fromList pcols
        PosSel _                -> $impossible

inferKeysBinOp :: S.Set PKey -> S.Set PKey -> Card1 -> Card1 -> BinOp -> S.Set PKey
inferKeysBinOp leftKeys rightKeys leftCard1 rightCard1 op =
    case op of
        Cross _      -> [ k | k <- leftKeys, rightCard1 ]
                        ∪
                        [ k | k <- rightKeys, leftCard1 ]
                        ∪
                        [ k1 ∪ k2 | k1 <- leftKeys, k2 <- rightKeys ]
        EqJoin (a, b) -> [ k | k <- leftKeys, rightCard1 ]
                         ∪
                         [ k | k <- rightKeys, leftCard1 ]
                         ∪
                         [ k | k <- leftKeys, (ss b) ∈ rightKeys ]
                         ∪
                         [ k | k <- rightKeys, (ss a) ∈ leftKeys ]
                         ∪
                         [ ( k1 ∖ (ss a)) ∪ k2
                         | (ss b) ∈ rightKeys
                         , k1 <- leftKeys
                         , k2 <- rightKeys
                         ]
                         ∪
                         [ k1 ∪ (k2 ∖ (ss b))
                         | (ss a) ∈ leftKeys
                         , k1 <- leftKeys
                         , k2 <- rightKeys
                         ]
                         ∪
                         [ k1 ∪ k2 | k1 <- leftKeys, k2 <- rightKeys ]
                         
        ThetaJoin preds -> [ k | k <- leftKeys, rightCard1 ]
                           ∪
                           [ k | k <- rightKeys, leftCard1 ]
                           ∪
                           [ k 
                           | k <- leftKeys
                           , (_, b, EqJ) <- S.fromList preds
                           , (ss b) ∈ rightKeys
                           ]
                           ∪
                           [ k 
                           | k <- rightKeys
                           , (a, _, EqJ) <- S.fromList preds
                           , (ss a) ∈ leftKeys
                           ]
                           ∪
                           [ k1 ∪ k2 | k1 <- leftKeys, k2 <- rightKeys ]
                  
        SemiJoin _    -> leftKeys
        AntiJoin _    -> leftKeys
        DisjUnion _   -> S.empty -- FIXME need domain property.
        Difference _  -> leftKeys


