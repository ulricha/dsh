{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE MonadComprehensions #-}

-- | Infer the input columns required in TableAlgebra plans.
module Database.DSH.Optimizer.TA.Properties.ICols where

import qualified Data.Set.Monad as S

import           Database.DSH.Impossible

import           Database.Algebra.Pathfinder.Data.Algebra

import Database.DSH.Optimizer.TA.Properties.Aux

exprCols :: Expr -> S.Set AttrName
exprCols (BinAppE _ e1 e2) = (exprCols e1) ∪ (exprCols e2)
exprCols (UnAppE _ e)      = exprCols e
exprCols (ColE c)          = S.singleton c
exprCols (ConstE _)        = S.empty

aggrInput :: AggrType -> S.Set AttrName
aggrInput (Avg c)  = S.singleton c
aggrInput (Max c)  = S.singleton c
aggrInput (Min c)  = S.singleton c
aggrInput (Sum c)  = S.singleton c
aggrInput (All c)  = S.singleton c
aggrInput (Prod c) = S.singleton c
aggrInput (Dist c) = S.singleton c
aggrInput Count    = S.empty

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
            if resCol ∈ ownICols
            then (S.delete resCol ownICols)
                  ∪ (S.fromList $ map fst sortInf) 
                  ∪ maybe S.empty S.singleton groupCol
                  ∪ childICols
            else (S.delete resCol ownICols) ∪ childICols
    
        RowRank (resCol, sortInf)   ->
            if resCol ∈ ownICols
            then (S.delete resCol ownICols)
                  ∪ (S.fromList $ map fst sortInf)
                  ∪ childICols
            else (S.delete resCol ownICols) ∪ childICols
        Rank (resCol, sortInf)      -> 
            if resCol ∈ ownICols
            then (S.delete resCol ownICols)
                  ∪ (S.fromList $ map fst sortInf)
                  ∪ childICols
            else (S.delete resCol ownICols) ∪ childICols

        -- For projections we require input columns of expressions, but only for
        -- those output columns which are actually required from downstream.
        Project projs         -> S.foldr (∪) childICols
                                 [ exprCols e 
                                 | (a, e) <- S.fromList projs
                                 , a ∈ ownICols 
                                 ]

        -- Require all columns for the select columns, in addition to columns
        -- required downstream
        Select e              -> childICols ∪ ownICols ∪ exprCols e
        Distinct _            -> childICols ∪ ownICols

        Aggr (acols, mpcol)   -> S.foldr (∪) childICols [ aggrInput agg 
                                                        | (agg, a) <- S.fromList acols
                                                        , a `S.member` ownICols 
                                                        ]
                                 ∪
                                 maybe S.empty S.singleton mpcol

        PosSel _              -> $impossible
