-- | Some auxiliary functions for property inference.
module Database.DSH.Optimizer.TA.Properties.Aux where

import qualified Data.Set.Monad as S

(∪) :: Ord a => S.Set a -> S.Set a -> S.Set a
(∪) = S.union

(∩) :: Ord a => S.Set a -> S.Set a -> S.Set a
(∩) = S.intersection

(∖) :: Ord a => S.Set a -> S.Set a -> S.Set a
(∖) = S.difference

(∈) :: Ord a => a -> S.Set a -> Bool
(∈) = S.member

(⊆) :: Ord a => S.Set a -> S.Set a -> Bool
(⊆) = S.isSubsetOf

-- | Singleton set abbreviation
ss :: Ord a => a -> S.Set a
ss = S.singleton

-- | List set abbreviation
ls :: Ord a => [a] -> S.Set a
ls = S.fromList

unionss :: Ord a => S.Set (S.Set a) -> S.Set a
unionss = S.foldr (∪) S.empty

