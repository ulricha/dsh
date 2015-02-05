{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE TemplateHaskell     #-}

-- | Infer columns whose exact values are required to compute the
-- correct result.
module Database.DSH.Backend.Sql.Opt.Properties.Use where

import qualified Data.Set.Monad                           as S

import           Database.Algebra.Table.Lang

import           Database.DSH.Backend.Sql.Opt.Properties.Auxiliary

flatten :: S.Set (S.Set Attr) -> S.Set Attr
flatten = S.foldl' (∪) S.empty


inferUseBinOp :: S.Set Attr
              -> S.Set Attr
              -> S.Set Attr
              -> S.Set Attr
              -> S.Set Attr
              -> BinOp
              -> (S.Set Attr, S.Set Attr)
inferUseBinOp ownUse leftUse rightUse leftCols rightCols op =
    case op of
         Cross _      -> ( leftUse ∪ [ c | c <- leftCols, c ∈ ownUse ]
                         , rightUse ∪ [ c | c <- rightCols, c ∈ ownUse ] )

         EqJoin (jc1, jc2) -> ( leftUse ∪ (ss jc1) ∪ [ c | c <- leftCols, c ∈ ownUse ]
                              , rightUse ∪ (ss jc2) ∪ [ c | c <- rightCols, c ∈ ownUse ] )
         ThetaJoin ps -> ( leftUse
                           ∪
                           flatten [ exprCols a | (a, _, _) <- S.fromList ps ]
                           ∪
                           [ c | c <- leftCols, c ∈ ownUse ]
                         , rightUse
                           ∪
                           flatten [ exprCols b | (_, b, _) <- S.fromList ps ]
                           ∪
                           [ c | c <- rightCols, c ∈ ownUse ]
                         )
         SemiJoin ps  -> ( leftUse
                           ∪
                           flatten [ exprCols a | (a, _, _) <- S.fromList ps ]
                           ∪
                           [ c | c <- leftCols, c ∈ ownUse ]
                         , rightUse
                           ∪
                           flatten [ exprCols b | (_, b, _) <- S.fromList ps ]
                         )
         AntiJoin ps  -> ( leftUse
                           ∪
                           flatten [ exprCols a | (a, _, _) <- S.fromList ps ]
                           ∪
                           [ c | c <- leftCols, c ∈ ownUse ]
                         , rightUse
                           ∪
                           flatten [ exprCols b | (_, b, _) <- S.fromList ps ])

         DisjUnion _  -> ( leftUse ∪ leftCols, rightUse ∪ rightCols )
         Difference _ -> ( leftUse ∪ leftCols, rightUse ∪ rightCols )

absPos :: SerializeOrder -> S.Set Attr
absPos (AbsPos c) = S.singleton c
absPos (RelPos _) = S.empty
absPos NoPos      = S.empty

inferUseUnOp :: S.Set Attr -> S.Set Attr -> UnOp -> S.Set Attr
inferUseUnOp ownUse childUse op =
    case op of
        WinFun ((resCol, winFun), partExprs, sortCols, _) ->
            childUse
            ∪ (S.delete resCol ownUse)
            ∪ (S.unions $ map exprCols partExprs)
            ∪ (S.unions $ map (exprCols . fst) sortCols)
            ∪ (winFunInput winFun)
        RowNum (resCol, _, _)     -> childUse ∪ (S.delete resCol ownUse)
        RowRank (resCol, _)       -> childUse ∪ (S.delete resCol ownUse)
        Rank (resCol, _)          -> childUse ∪ (S.delete resCol ownUse)
        Project projs             -> childUse
                                     ∪ (unionss [ exprCols e | (a, e) <- S.fromList projs, a ∈ ownUse ])
        Select e                  -> childUse ∪ ownUse ∪ (exprCols e)
        Distinct _                -> childUse ∪ ownUse

        -- FIXME unconditionally declaring pcols as used might be a bit too defensive.
        Aggr (acols, pexprs)      -> (S.unions $ map (exprCols . snd) pexprs)
                                     ∪
                                     (S.unions $ map (aggrInput . fst) acols)

        Serialize (md, mp, cs)    -> childUse
                                     ∪ (S.fromList $ map (\(PayloadCol c) -> c) cs)
                                     ∪ (maybe S.empty (\(DescrCol c) -> S.singleton c) md)
                                     -- FIXME once order and -- surrogates are decoupled, absolute pos
                                     -- values are no longer required.
                                     ∪ absPos mp
