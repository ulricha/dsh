-- | Some auxiliary functions for property inference.
module Database.DSH.Optimizer.TA.Properties.Aux where

import qualified Data.Set.Monad              as S

import           Database.Algebra.Table.Lang

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

exprCols :: Expr -> S.Set Attr
exprCols (BinAppE _ e1 e2) = exprCols e1 ∪ exprCols e2
exprCols (IfE c t e)       = exprCols c ∪ exprCols t ∪ exprCols e
exprCols (UnAppE _ e)      = exprCols e
exprCols (ColE c)          = S.singleton c
exprCols (ConstE _)        = S.empty

aggrInput :: AggrType -> S.Set Attr
aggrInput (Avg e)  = exprCols e
aggrInput (Max e)  = exprCols e
aggrInput (Min e)  = exprCols e
aggrInput (Sum e)  = exprCols e
aggrInput (All e)  = exprCols e
aggrInput (Any e)  = exprCols e
aggrInput Count    = S.empty

winFunInput :: WinFun -> S.Set Attr
winFunInput (WinAvg e)  = exprCols e
winFunInput (WinMax e)  = exprCols e
winFunInput (WinMin e)  = exprCols e
winFunInput (WinSum e)  = exprCols e
winFunInput (WinAll e)  = exprCols e
winFunInput (WinAny e)  = exprCols e
winFunInput WinCount    = S.empty

mapCol :: Proj -> Maybe (Attr, Attr)
mapCol (a, ColE b) = Just (a, b)
mapCol _           = Nothing

mColE :: Expr -> Maybe Attr
mColE (ColE c) = Just c
mColE _        = Nothing

posCol :: SerializeOrder -> S.Set Attr
posCol (AbsPos c)  = S.singleton c
posCol (RelPos cs) = S.fromList cs
posCol NoPos       = S.empty
