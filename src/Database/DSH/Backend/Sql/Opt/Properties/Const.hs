{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE TemplateHaskell     #-}

module Database.DSH.Backend.Sql.Opt.Properties.Const
    ( inferConstNullOp
    , inferConstUnOp
    , inferConstBinOp
    , constExpr
    ) where

import           Data.Maybe
import           Data.List

import           Database.Algebra.Table.Lang

import           Database.DSH.Backend.Sql.Opt.Properties.Types

constExpr :: [ConstCol] -> Expr -> Maybe AVal
constExpr _         (BinAppE _ _ _) = Nothing
constExpr _         (UnAppE _ _)    = Nothing
constExpr constCols (ColE c)        = lookup c constCols
constExpr _         (ConstE v)      = Just v
constExpr _         (IfE _ _ _)     = Nothing

constProj :: [ConstCol] -> (Attr, Expr) -> Maybe ConstCol
constProj constCols (c, e) = constExpr constCols e >>= \v -> return (c, v)

inferConstNullOp :: NullOp -> [ConstCol]
inferConstNullOp op =
    case op of
        LitTable (tuples, schema) -> concat $ zipWith constCol (transpose tuples) (map fst schema)
          where
            constCol (v:vs) c | all (== v) vs = [(c, v)]
            constCol _      _                 = []
        TableRef _             -> []

inferConstSelect :: Expr -> [ConstCol]
inferConstSelect (BinAppE Eq (ColE c) (ConstE v)) = [(c, v)]
inferConstSelect (BinAppE Eq (ConstE v) (ColE c)) = [(c, v)]
inferConstSelect (BinAppE And e1 e2)              = inferConstSelect e1 ++ inferConstSelect e2
inferConstSelect _                                = []

inferConstUnOp :: [ConstCol] -> UnOp -> [ConstCol]
inferConstUnOp childConst op = 
    case op of
        WinFun _          -> childConst
        RowNum (_, _, _)  -> childConst
        RowRank (_, _)    -> childConst
        Rank (_, _)       -> childConst
        Select p          -> inferConstSelect p ++ childConst
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

