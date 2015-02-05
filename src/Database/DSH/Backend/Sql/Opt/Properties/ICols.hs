{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE TemplateHaskell     #-}

-- | Infer the input columns required in TableAlgebra plans.
module Database.DSH.Backend.Sql.Opt.Properties.ICols where

import qualified Data.Set.Monad                           as S

import           Database.Algebra.Table.Lang

import           Database.DSH.Backend.Sql.Opt.Properties.Auxiliary

inferIColsBinOp :: S.Set Attr  -- ^ columns that are required from us
                -> S.Set Attr  -- ^ Columns required from the left child
                -> S.Set Attr  -- ^ Output of the left child
                -> S.Set Attr  -- ^ Columns required from the right child
                -> S.Set Attr  -- ^ Output of the left child
                -> BinOp       -- ^ The operator
                -> (S.Set Attr, S.Set Attr)
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
             let leftExprCols = S.unions $ map (\(l, _, _) -> exprCols l) cs
                 rightExprCols = S.unions $ map (\(_, r, _) -> exprCols r) cs

                 leftICols' = leftICols ∪ (ownICols ∩ leftCols) ∪ leftExprCols
                 rightICols' = rightICols ∪ (ownICols ∩ rightCols) ∪ rightExprCols
             in (leftICols', rightICols')

         -- From the left, we require all columns required by us, in addition to
         -- the left join columns.
         SemiJoin cs ->
             let leftExprCols = S.unions $ map (\(l, _, _) -> exprCols l) cs
                 rightExprCols = S.unions $ map (\(_, r, _) -> exprCols r) cs

                 leftICols' = leftICols ∪ ownICols ∪ leftExprCols
                 rightICols' = rightExprCols
             in (leftICols', rightICols')
         AntiJoin cs ->
             let leftExprCols = S.unions $ map (\(l, _, _) -> exprCols l) cs
                 rightExprCols = S.unions $ map (\(_, r, _) -> exprCols r) cs

                 leftICols' = leftICols ∪ ownICols ∪ leftExprCols
                 rightICols' = rightExprCols
             in (leftICols', rightICols')

         -- The schemata of both union inputs must be kept in sync. No
         -- ICols-based (i.e. colummn-pruning) rewrites can be
         -- performed unless there is a guarantee that they happen in
         -- both branches.
         DisjUnion _  -> (leftCols, rightCols)

         Difference _ -> (leftICols ∪ leftCols, rightICols ∪ leftCols)

inferIColsUnOp :: S.Set Attr -> S.Set Attr -> UnOp -> S.Set Attr
inferIColsUnOp ownICols childICols op =
    case op of
        WinFun ((resCol, fun), partExprs, sortInf, _) ->
            (S.delete resCol ownICols)
            ∪ (winFunInput fun)
            ∪ (S.unions $ map (exprCols . fst) sortInf)
            ∪ (S.unions $ map exprCols partExprs)
            ∪ childICols
        -- Require the sorting columns, if the rownum output is required.
        RowNum (resCol, sortInf, groupExprs) ->
            (S.delete resCol ownICols)
            ∪ (S.unions $ map (exprCols . fst) sortInf)
            ∪ (S.unions $ map exprCols groupExprs)
            ∪ childICols

        RowRank (resCol, sortInf)   ->
            (S.delete resCol ownICols)
            ∪ (S.unions $ map (exprCols . fst) sortInf)
            ∪ childICols
        Rank (resCol, sortInf)      ->
            (S.delete resCol ownICols)
            ∪ (S.unions $ map (exprCols . fst) sortInf)
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

        Serialize cs          ->
            let (mDescr, mPos, cols) = cs
            in childICols
               ∪ (S.fromList $ map (\(PayloadCol c) -> c) cols)
               ∪ (maybe S.empty (\(DescrCol c) -> S.singleton c) mDescr)
               ∪ posCol mPos
