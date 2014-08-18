{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE TemplateHaskell     #-}

module Database.DSH.Optimizer.TA.Properties.Const where

import           Data.Maybe
import qualified Data.Set.Monad                             as S
import           Data.Tuple
import           Data.List

import           Database.Algebra.Table.Lang

import           Database.DSH.Impossible

import           Database.DSH.Optimizer.TA.Properties.Aux
import           Database.DSH.Optimizer.TA.Properties.Types

constExpr :: [ConstCol] -> Expr -> Maybe AVal
constExpr constCols (BinAppE f e1 e2) = Nothing
constExpr constCols (UnAppE f e)      = Nothing
constExpr constCols (ColE c)          = lookup c constCols
constExpr constCols (ConstE v)        = Just v
constExpr constCols (IfE c t e)       = Nothing

constProj :: [ConstCol] -> (Attr, Expr) -> Maybe ConstCol
constProj constCols (c, e) = constExpr constCols e >>= \v -> return (c, v)

inferConstNullOp :: NullOp -> [ConstCol]
inferConstNullOp op =
    case op of
        LitTable tuples schema -> concat $ zipWith constCol (transpose tuples) (map fst schema)
          where
            constCol (v:vs) c | all (== v) vs = [(c, v)]
            constCol _      _                 = []
        TableRef _             -> []


inferConstUnOp :: [ConstCol] -> UnOp -> [ConstCol]
inferConstUnOp childConst op = 
    case op of
        WinFun _          -> childConst
        RowNum (_, _, _)  -> childConst
        RowRank (_, _)    -> childConst
        Rank (_, _)       -> childConst
        Select _          -> childConst
        Distinct _        -> childConst
        Aggr _            -> []
        Project projs     -> mapMaybe (constProj childConst) projs
        Serialize _       -> childConst

inferConstBinOp :: [ConstCol] -> [ConstCol] -> BinOp -> [ConstCol]
inferConstBinOp leftChildConst rightChildConst op =
    case op of
        Cross _      -> leftChildConst ++ rightChildConst
        EqJoin _     -> leftChildConst ++ rightChildConst
        ThetaJoin _  -> leftChildConst ++ rightChildConst
        SemiJoin _   -> leftChildConst
        AntiJoin _   -> leftChildConst
        DisjUnion _  -> [ (c1, v1)
                        | (c1, v1) <- leftChildConst
                        , (c2, v2) <- rightChildConst
                        , c1 == c2
                        , v1 == v2
                        ]
        Difference _ -> leftChildConst

