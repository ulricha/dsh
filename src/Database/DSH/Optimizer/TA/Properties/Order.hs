{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE TemplateHaskell     #-}

module Database.DSH.Optimizer.TA.Properties.Order where

import           Data.Maybe
import qualified Data.Set.Monad                             as S
import           Data.Tuple

import           Database.Algebra.Table.Lang

import           Database.DSH.Impossible

import           Database.DSH.Optimizer.TA.Properties.Aux
import           Database.DSH.Optimizer.TA.Properties.Types

-- | Column 'c' has been overwritten by the current operator. Remove
-- all associated sorting information.
invalidate :: Attr -> Orders -> Orders
invalidate c order = [ o | o@(c', _) <- order, c /= c' ]

-- | Overwrite (if present) order information for column 'o' with new
-- information.
-- FIXME Handle case of arbitrary expressions defining order.
overwrite :: (Attr, [Expr]) -> Orders -> Orders
overwrite (resCol, ordExprs) os =
    if all isJust mOrdCols
    -- Check if the result column overwrites some older order column
    then if any ((== resCol) . fst) os
         then [ (resCol, ordCols) | (oc, _) <- os, oc == resCol ]
         else (resCol, ordCols) : os
    -- The order is defined by non-column expressions. We don't handle
    -- that case currently.
    else os

  where
    mOrdCols = map mColE ordExprs
    ordCols  = catMaybes mOrdCols

-- | Produce all new sorting columns from the list of new names per
-- old sorting column:
-- [[a, b, c], [d, e], [f]] => [[a, d, f], [a, e, f], [b, d, f], ...]
-- [[a, b, c], [], [f]]     => []
ordCombinations :: [[Attr]] -> [[Attr]]
ordCombinations []        = $impossible
ordCombinations (s : [])  = map (: []) s
ordCombinations (s : scs) = dist s (ordCombinations scs)

  where
    dist :: [Attr] -> [[Attr]] -> [[Attr]]
    dist as bs = [ a : b | a <- as, b <- bs ]

-- | Find all new names for column 'c'.
newCols :: [(Attr, Attr)] -> Attr -> [Attr]
newCols colMap c = [ cn | (co, cn) <- colMap, co == c ]

-- | Refresh order information with new names for the order column and
-- new names for the sorting columns.
update :: [(Attr, Attr)] -> (Attr, [Attr]) -> Orders
update colMap (ordCol, sortCols) =
    let ordCols'  = newCols colMap ordCol
        sortCols' = map (newCols colMap) sortCols

    in if any null sortCols'
       then []
       else [ (oc, scs) | oc <- ordCols', scs <- ordCombinations sortCols' ]

inferOrderUnOp :: Orders -> UnOp -> Orders
inferOrderUnOp childOrder op =
    case op of
        WinFun _                          -> childOrder
        RowNum (oc, scs, [])
             | not (null scs) 
               -- Only consider ascending sorting
               && all ((== Asc) . snd) scs
               -- Avoid circular references
               && (ColE oc) `notElem` (map fst scs)
                                          -> overwrite (oc, map fst scs) childOrder
             | otherwise
                                          -> invalidate oc childOrder
        RowNum (resCol, _, _)             -> invalidate resCol childOrder
        RowRank (resCol, _)               -> invalidate resCol childOrder
        Rank (resCol, _)                  -> invalidate resCol childOrder
        Select _                          -> childOrder
        Distinct _                        -> childOrder
        Aggr _                            -> []
        Project projs                     ->
            let colMap = S.toList $ S.map swap $ S.fromList $ mapMaybe mapCol projs
            in concatMap (update colMap) childOrder
        Serialize _                       -> []

inferOrderBinOp :: Orders -> Orders -> BinOp -> Orders
inferOrderBinOp leftChildOrder rightChildOrder op =
    case op of
        Cross _      -> leftChildOrder ++ rightChildOrder
        EqJoin _     -> leftChildOrder ++ rightChildOrder
        ThetaJoin _  -> leftChildOrder ++ rightChildOrder
        SemiJoin _   -> leftChildOrder
        AntiJoin _   -> leftChildOrder
        DisjUnion _  -> []
        Difference _ -> leftChildOrder

