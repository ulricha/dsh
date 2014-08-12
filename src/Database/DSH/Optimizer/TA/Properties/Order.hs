{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE MonadComprehensions #-}

module Database.DSH.Optimizer.TA.Properties.Order where

import Data.Tuple
import qualified Data.Set.Monad as S

import Database.Algebra.Table.Lang

import Database.DSH.Impossible

import Database.DSH.Optimizer.TA.Properties.Aux
import Database.DSH.Optimizer.TA.Properties.Types

-- | Column 'c' has been overwritten by the current operator. Remove
-- all associated sorting information.
invalidate :: Attr -> Orders -> Orders
invalidate c order = [ o | o@(c', _) <- order, c /= c' ]

-- | Overwrite (if present) order information for column 'o' with new
-- information.
overwrite :: (Attr, [Attr]) -> Orders -> Orders
overwrite o@(ordCol, _) os = 
    if any ((== ordCol) . fst) os
    then [ o | (oc, _) <- os, oc == ordCol ]
    else o : os

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
        RowNum (oc, scs, Nothing) 
             | not (null scs) && all ((== Asc) . snd) scs 
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
            let colMap = S.toList $ S.map swap $ S.unions $ map mapCol projs
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
        
