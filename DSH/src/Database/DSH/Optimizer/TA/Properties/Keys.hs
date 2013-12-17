-- FIXME once 7.8 is out, use overloaded list notation for sets
-- instead of S.fromList!
{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE TemplateHaskell     #-}

module Database.DSH.Optimizer.TA.Properties.Keys where

import Data.List
import qualified Data.Set.Monad as S

import           Database.DSH.Impossible

import           Database.Algebra.Pathfinder.Data.Algebra

import           Database.DSH.Optimizer.TA.Properties.Aux
import           Database.DSH.Optimizer.TA.Properties.Types

sk :: AttrName -> PKey
sk = S.singleton

lk :: [AttrName] -> PKey
lk = S.fromList

mapCol :: Proj -> S.Set (AttrName, AttrName)
mapCol (a, ColE b) = S.singleton (a, b)
mapCol _           = S.empty

-- | Compute keys for rank and rowrank operators
rowRankKeys :: AttrName -> S.Set AttrName -> Card1 -> S.Set PKey -> S.Set PKey
rowRankKeys resCol sortCols childCard1 childKeys =
    -- All old keys stay intact
    childKeys
    ∪
    -- Trivial case: singleton input
    [ sk resCol | childCard1 ]
    ∪
    -- If sorting columns form a part of a key, the output column
    -- combined with the key columns that are not sorting columns also
    -- is a key.
    [ (sk resCol) ∪ (k ∖ sortCols)
    | k <- childKeys
    , k ∩ sortCols /= S.empty
    ]

inferKeysNullOp :: NullOp -> S.Set PKey
inferKeysNullOp op =
    case op of
        -- FIXME check all combinations of columns for uniqueness
        LitTable vals schema  -> S.fromList
                                 $ map (sk . snd) 
                                 $ filter (isUnique . fst)
                                 $ zip (transpose vals) (map fst schema)
          where
            isUnique :: [AVal] -> Bool
            isUnique vals = (length $ nub vals) == (length vals)

        EmptyTable _          -> S.empty
        TableRef (_, _, keys) -> S.fromList $ map (\(Key k) -> lk k) keys

inferKeysUnOp :: S.Set PKey -> Card1 -> S.Set AttrName -> UnOp -> S.Set PKey
inferKeysUnOp childKeys childCard1 childCols op =
    case op of
        RowNum (resCol, _, Nothing)    -> S.insert (sk resCol) childKeys
        RowNum (resCol, _, Just pattr) -> (S.singleton $ lk [resCol, pattr])
                                          ∪
                                          [ sk resCol | childCard1 ]
                                          ∪
                                          childKeys
        RowRank (resCol, sortInfo)     -> rowRankKeys resCol (lk $ map fst sortInfo) childCard1 childKeys
        Rank (resCol, sortInfo)        -> rowRankKeys resCol (lk $ map fst sortInfo) childCard1 childKeys

        -- This is just the standard Pathfinder way: we take all keys
        -- whose columns survive the projection and update to the new
        -- attr names. We could consider all expressions, but need to
        -- be careful here as not all operators might be injective.
        Project projs           -> [ [ a | (a, b) <- attrPairs , b ∈ k ]
                                   | k <- childKeys
                                   , let attrPairs = S.unions $ map mapCol projs
                                   , k ⊆ [ snd x | x <- attrPairs ]
                                   ]

        Select _                -> childKeys
        Distinct _              -> S.insert childCols childKeys 
        Aggr (_, Just gcol)     -> S.singleton $ sk gcol
        Aggr (_, Nothing)       -> S.empty
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
                         [ k | k <- leftKeys, (sk b) ∈ rightKeys ]
                         ∪
                         [ k | k <- rightKeys, (sk a) ∈ leftKeys ]
                         ∪
                         [ ( k1 ∖ (sk a)) ∪ k2
                         | (sk b) ∈ rightKeys
                         , k1 <- leftKeys
                         , k2 <- rightKeys
                         ]
                         ∪
                         [ k1 ∪ (k2 ∖ (sk b))
                         | (sk a) ∈ leftKeys
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
                           , (sk b) ∈ rightKeys
                           ]
                           ∪
                           [ k 
                           | k <- rightKeys
                           , (a, _, EqJ) <- S.fromList preds
                           , (sk a) ∈ leftKeys
                           ]
                           ∪
                           [ k1 ∪ k2 | k1 <- leftKeys, k2 <- rightKeys ]
                  
        SemiJoin _    -> leftKeys
        AntiJoin _    -> leftKeys
        DisjUnion _   -> S.empty -- FIXME need domain property.
        Difference _  -> leftKeys


