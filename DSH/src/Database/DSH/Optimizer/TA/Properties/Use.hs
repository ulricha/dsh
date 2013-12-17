{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE MonadComprehensions #-}

-- | Infer columns whose exact values are required to compute the
-- correct result.
module Database.DSH.Optimizer.TA.Properties.Use where

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

inferUseBinOp :: S.Set AttrName    
                -> S.Set AttrName  
                -> S.Set AttrName  
                -> S.Set AttrName  
                -> S.Set AttrName  
                -> BinOp           
                -> (S.Set AttrName, S.Set AttrName)
inferUseBinOp ownUse leftUse rightUse leftCols rightCols op = 
    case op of
         Cross _      -> ( leftUse ∪ [ c | c <- leftCols, c ∈ ownUse ]
                         , rightUse ∪ [ c | c <- rightCols, c ∈ ownUse ] )
    
         EqJoin (jc1, jc2) -> ( leftUse ∪ (ss jc1) ∪ [ c | c <- leftCols, c ∈ ownUse ]
                              , rightUse ∪ (ss jc2) ∪ [ c | c <- rightCols, c ∈ ownUse ] )
         ThetaJoin ps -> ( leftUse 
                           ∪ 
                           [ a | (a, _, _) <- S.fromList ps ]
                           ∪ 
                           [ c | c <- leftCols, c ∈ ownUse ]
                         , rightUse 
                           ∪ 
                           [ b | (_, b, _) <- S.fromList ps ]
                           ∪ 
                           [ c | c <- rightCols, c ∈ ownUse ]
                         )
         SemiJoin ps  -> ( leftUse
                           ∪ 
                           [ a | (a, _, _) <- S.fromList ps ]
                           ∪ 
                           [ c | c <- leftCols, c ∈ ownUse ]
                         , rightUse
                           ∪
                           [ b | (_, b, _) <- S.fromList ps ]
                         )
         AntiJoin ps  -> ( leftUse
                           ∪ 
                           [ a | (a, _, _) <- S.fromList ps ]
                           ∪ 
                           [ c | c <- leftCols, c ∈ ownUse ]
                         , rightUse
                           ∪
                           [ b | (_, b, _) <- S.fromList ps ])

         DisjUnion _  -> ( leftUse ∪ leftCols, rightUse ∪ rightCols )
         Difference _ -> ( leftUse ∪ leftCols, rightUse ∪ rightCols )
                
inferUseUnOp :: S.Set AttrName -> S.Set AttrName -> UnOp -> S.Set AttrName
inferUseUnOp ownUse childUse op = 
    case op of
        RowNum (resCol, _, _) -> childUse ∪ (S.delete resCol ownUse)
    
        RowRank (resCol, _)   -> childUse ∪ (S.delete resCol ownUse)
        Rank (resCol, _)      -> childUse ∪ (S.delete resCol ownUse)
        Project projs         -> childUse 
                                 ∪ (unionss [ exprCols e | (a, e) <- S.fromList projs, a ∈ ownUse ])
        Select e              -> childUse ∪ ownUse ∪ (exprCols e)
        Distinct _            -> childUse ∪ ownUse 

        Aggr (acols, Just pcol) -> [ pcol | pcol ∈ ownUse ] 
                                   ∪ (S.unions $ map (aggrInput . fst) acols)
                                   ∪ [ pcol | pcol ∈ ownUse ]

        Aggr (acols, Nothing)   -> S.unions $ map (aggrInput . fst) acols

        PosSel _              -> $impossible
