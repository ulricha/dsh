{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TemplateHaskell       #-}

module Database.DSH.NKL.Lang
  ( Expr(..)
  , Typed(..)
  , Prim1(..)
  , Prim2(..)
  ) where

import           Text.PrettyPrint.ANSI.Leijen
import           Text.Printf

import           Database.DSH.Common.Impossible
import qualified Database.DSH.Common.Lang       as L
import           Database.DSH.Common.Nat
import           Database.DSH.Common.Pretty
import           Database.DSH.Common.Type       (Type, Typed, typeOf)

-- | Nested Kernel Language (NKL) expressions
data Expr  = Table Type String L.BaseTableSchema
           | AppE1 Type Prim1 Expr
           | AppE2 Type Prim2 Expr Expr
           | BinOp Type L.ScalarBinOp Expr Expr
           | UnOp Type L.ScalarUnOp Expr
           | If Type Expr Expr Expr
           | Const Type L.Val
           | Var Type L.Ident
           | Iterator Type Expr L.Ident Expr
           | Let Type L.Ident Expr Expr
           | MkTuple Type [Expr]
           deriving (Show)

instance Typed Expr where
    typeOf (Table t _ _)      = t
    typeOf (AppE1 t _ _)      = t
    typeOf (AppE2 t _ _ _)    = t
    typeOf (If t _ _ _)       = t
    typeOf (BinOp t _ _ _)    = t
    typeOf (UnOp t _ _)       = t
    typeOf (Const t _)        = t
    typeOf (Var t _)          = t
    typeOf (Iterator t _ _ _) = t
    typeOf (Let t _ _ _)      = t
    typeOf (MkTuple t _)      = t

instance Pretty Expr where
    pretty (MkTuple _ es)      = prettyTuple $ map pretty es
    pretty (AppE1 _ (TupElem n) e1) =
        parenthize e1 <> dot <> int (tupleIndex n)
    pretty (Table _ n _)       = kw (text "table") <> parens (text n)
    pretty (AppE1 _ p1 e)      = pretty p1 <+> parenthize e
    pretty (AppE2 _ p2 e1 e2)
        | isJoinOp p2 = prettyJoin (pretty p2) (parenthize e1) (parenthize e2)
        | otherwise   = prettyApp2 (pretty p2) (parenthize e1) (parenthize e2)
    pretty (UnOp _ o e)        = prettyUnOp (pretty o) (pretty e)
    pretty (BinOp _ o e1 e2)
        | L.isBinInfixOp o = prettyInfixBinOp (pretty o)
                                              (parenthize e1)
                                              (parenthize e2)
        | otherwise        = prettyPrefixBinOp (pretty o)
                                               (parenthize e1)
                                               (parenthize e2)
    pretty (If _ c t e)        = prettyIf (pretty c) (pretty t) (pretty e)
    pretty (Const _ v)         = pretty v
    pretty (Var _ s)           = text s
    pretty (Iterator _ e x xs) =
        prettyComp (pretty e) [text x <+> comp (text "<-") <+> pretty xs]
    pretty (Let _ x e1 e)      = prettyLet (text x) (pretty e1) (pretty e)

parenthize :: Expr -> Doc
parenthize e =
    case e of
        Var{}                 -> pretty e
        Const{}               -> pretty e
        Table{}               -> pretty e
        Iterator{}            -> pretty e
        AppE1 _ (TupElem _) _ -> pretty e
        _                     -> parens $ pretty e

data Prim1 = Singleton
           | Only
           | Concat
           | Reverse
           | Nub
           | Number
           | Sort
           | Group
           | Restrict
           | TupElem TupleIndex
           | Agg L.AggrFun
           deriving (Eq, Show)

instance Pretty Prim1 where
    pretty Singleton       = combinator $ text "sng"
    pretty Only            = combinator $ text "only"
    pretty Concat          = combinator $ text "concat"
    pretty Reverse         = combinator $ text "reverse"
    pretty Nub             = combinator $ text "nub"
    pretty Number          = combinator $ text "number"
    pretty Sort            = combinator $ text "sort"
    pretty Restrict        = restrict $ text "restrict"
    pretty Group           = combinator $ text "group"
    pretty (Agg a)         = pretty a
    -- tuple access is pretty-printed in a special way
    pretty TupElem{}       = $impossible

data Prim2 = Append
           | Zip
           | CartProduct
           | NestProduct
           | ThetaJoin (L.JoinPredicate L.ScalarExpr)
           | NestJoin (L.JoinPredicate L.ScalarExpr)
           | GroupJoin (L.JoinPredicate L.ScalarExpr) (L.NE L.AggrApp)
           | SemiJoin (L.JoinPredicate L.ScalarExpr)
           | AntiJoin (L.JoinPredicate L.ScalarExpr)
           deriving (Eq, Show)

isJoinOp :: Prim2 -> Bool
isJoinOp op =
    case op of
        CartProduct -> True
        NestProduct -> True
        ThetaJoin{} -> True
        NestJoin{}  -> True
        GroupJoin{} -> True
        SemiJoin{}  -> True
        AntiJoin{}  -> True
        Append      -> False
        Zip         -> False

instance Pretty Prim2 where
    pretty Append          = combinator $ text "append"
    pretty Zip             = combinator $ text "zip"

    pretty CartProduct     = join $ text "cartproduct"
    pretty NestProduct     = join $ text "nestproduct"
    pretty (ThetaJoin p)   = join $ text $ printf "thetajoin{%s}" (pp p)
    pretty (NestJoin p)    = join $ text $ printf "nestjoin{%s}" (pp p)
    pretty (GroupJoin p a) = join $ text $ printf "groupjoin{%s, %s}" (pp p) (pp a)
    pretty (SemiJoin p)    = join $ text $ printf "semijoin{%s}" (pp p)
    pretty (AntiJoin p)    = join $ text $ printf "antijoin{%s}" (pp p)
