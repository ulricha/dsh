{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE MonadComprehensions #-}

-- | Infer the input columns required in TableAlgebra plans.
module Database.DSH.Optimizer.TA.Properties.ICols where

import qualified Data.Set.Monad as S

import           Database.Algebra.Pathfinder.Data.Algebra

import Database.DSH.Optimizer.TA.Properties.Aux

inferIColsBinOp :: S.Set AttrName  -- ^ columns that are required from us
                -> S.Set AttrName  -- ^ Columns required from the left child
                -> S.Set AttrName  -- ^ Output of the left child
                -> S.Set AttrName  -- ^ Columns required from the right child
                -> S.Set AttrName  -- ^ Output of the left child
                -> BinOp           -- ^ The operator
                -> (S.Set AttrName, S.Set AttrName)
inferIColsBinOp ownICols leftICols leftCols rightICols rightCols op = 
    case op of
         -- Require columns from the originating side.
         Cross _ -> ( leftICols ∪ (ownICols ∩ leftCols)
                    , rightICols ∪ (ownICols ∩ rightCols) )
    
         -- Require columns from the originating side, in addition to the join
         -- columns.
         EqJoin (leftJoinCol, rightJoinCol) -> 
             ( leftICols ∪ (ownICols ∩ leftCols) ∪ (S.singleton leftJoinCol)
             , rightICols ∪ (ownICols ∩rightCols) ∪ (S.singleton rightJoinCol) )
         ThetaJoin cs -> 
             let leftExprCols = S.fromList $ map (\(l, _, _) -> l) cs
                 rightExprCols = S.fromList $ map (\(_, r, _) -> r) cs

                 leftICols' = leftICols ∪ (ownICols ∩ leftCols) ∪ leftExprCols
                 rightICols' = rightICols ∪ (ownICols ∩ rightCols) ∪ rightExprCols
             in (leftICols', rightICols')

         -- From the left, we require all columns required by us, in addition to
         -- the left join columns.
         SemiJoin cs -> 
             let leftExprCols = S.fromList $ map (\(l, _, _) -> l) cs
                 rightExprCols = S.fromList $ map (\(_, r, _) -> r) cs

                 leftICols' = leftICols ∪ ownICols ∪ leftExprCols
                 rightICols' = rightExprCols
             in (leftICols', rightICols')
         AntiJoin cs -> 
             let leftExprCols = S.fromList $ map (\(l, _, _) -> l) cs
                 rightExprCols = S.fromList $ map (\(_, r, _) -> r) cs

                 leftICols' = leftICols ∪ ownICols ∪ leftExprCols
                 rightICols' = rightExprCols
             in (leftICols', rightICols')

         DisjUnion _  -> (leftICols ∪ ownICols, rightICols ∪ ownICols)
         Difference _ -> undefined
                
inferIColsUnOp :: S.Set AttrName -> S.Set AttrName -> UnOp -> S.Set AttrName
inferIColsUnOp ownICols childICols op = 
    case op of
        -- Require the sorting columns, if the rownum output is required.
        RowNum (resCol, sortInf, groupCol) -> 
            (S.delete resCol ownICols)
            ∪ (S.fromList $ map fst sortInf) 
            ∪ maybe S.empty S.singleton groupCol
            ∪ childICols
    
        RowRank (resCol, sortInf)   ->
            (S.delete resCol ownICols)
            ∪ (S.fromList $ map fst sortInf)
            ∪ childICols
        Rank (resCol, sortInf)      -> 
            (S.delete resCol ownICols)
            ∪ (S.fromList $ map fst sortInf)
            ∪ childICols

        -- For projections we require input columns of expressions, but only for
        -- those output columns which are actually required from downstream.
        Project projs         -> S.foldr (∪) childICols $ S.fromList $ map (exprCols . snd) projs

        -- Require all columns for the select columns, in addition to columns
        -- required downstream
        Select e              -> childICols ∪ ownICols ∪ exprCols e
        Distinct _            -> childICols ∪ ownICols

        Aggr (acols, pexprs)  -> (S.foldr (∪) childICols $ S.fromList $ map (aggrInput . fst) acols)
                                 ∪
                                 (S.foldr (∪) S.empty $ S.fromList $ map (exprCols . snd) pexprs)
