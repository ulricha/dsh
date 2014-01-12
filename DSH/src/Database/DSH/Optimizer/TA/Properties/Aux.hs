-- | Some auxiliary functions for property inference.
module Database.DSH.Optimizer.TA.Properties.Aux where

import Database.Algebra.Pathfinder.Data.Algebra

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

exprCols :: Expr -> S.Set AttrName
exprCols (BinAppE _ e1 e2) = (exprCols e1) ∪ (exprCols e2)
exprCols (UnAppE _ e)      = exprCols e
exprCols (ColE c)          = S.singleton c
exprCols (ConstE _)        = S.empty

aggrInput :: AggrType -> S.Set AttrName
aggrInput (Avg e)  = exprCols e
aggrInput (Max e)  = exprCols e
aggrInput (Min e)  = exprCols e
aggrInput (Sum e)  = exprCols e
aggrInput (All e)  = exprCols e
aggrInput (Prod e) = exprCols e
aggrInput (Dist e) = exprCols e
aggrInput Count    = S.empty

mapCol :: Proj -> S.Set (AttrName, AttrName)
mapCol (a, ColE b) = S.singleton (a, b)
mapCol _           = S.empty
