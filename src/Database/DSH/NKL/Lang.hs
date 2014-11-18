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

import           Database.DSH.Impossible
import qualified Database.DSH.Common.Lang     as L
import           Database.DSH.Common.Pretty
import           Database.DSH.Common.Nat
import           Database.DSH.Common.Type     (Type, Typed, typeOf)

-- | Nested Kernel Language (NKL) expressions
data Expr  = Table Type String [L.Column] L.TableHints
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
    typeOf (Table t _ _ _)    = t
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
    pretty (MkTuple _ es)      = tupled $ map pretty es
    pretty (AppE1 _ (TupElem n) e1) = 
        parenthize e1 <> dot <> int (tupleIndex n)
    pretty (Table _ n _ _)     = text "table" <> parens (text n)
    pretty (AppE1 _ p1 e)      = (text $ show p1) <+> (parenthize e)
    pretty (AppE2 _ p1 e1 e2)  = (text $ show p1) <+> (align $ (parenthize e1) </> (parenthize e2))
    pretty (BinOp _ o e1 e2)   = (parenthize e1) <+> (pretty o) <+> (parenthize e2)
    pretty (UnOp _ o e)        = text (show o) <> parens (pretty e)
    pretty (If _ c t e)        = text "if"
                                 <+> pretty c
                                 <+> text "then"
                                 <+> (parenthize t)
                                 <+> text "else"
                                 <+> (parenthize e)
    pretty (Const _ v)         = pretty v
    pretty (Var _ s)           = text s
    pretty (Iterator _ e x xs) = align 
                                $ brackets 
                                $ enclose (char ' ') (char ' ') 
                                $ pretty e </> char '|' <+> text x <+> text "<-" <+> pretty xs
    pretty (Let _ x e1 e)      = 
        align $ text "let" <+> text x <+> char '=' <+> pretty e1
                </>
                text "in" <+> pretty e

parenthize :: Expr -> Doc
parenthize e =
    case e of
        Var _ _               -> pretty e
        Const _ _             -> pretty e
        Table _ _ _ _         -> pretty e
        Iterator _ _ _ _      -> pretty e
        AppE1 _ (TupElem _) _ -> pretty e
        _                     -> parens $ pretty e

data Prim1 = Length 
           | Concat
           | Sum 
           | Avg 
           | The 
           | Head
           | Tail
           | Minimum 
           | Maximum
           | Reverse 
           | And 
           | Or
           | Init 
           | Last 
           | Nub
           | Number
           | Reshape Integer
           | Transpose
           | TupElem TupleIndex
           deriving (Eq)

instance Show Prim1 where
    show Length          = "length"
    show Concat          = "concat"
    show Sum             = "sum"
    show Avg             = "avg"
    show The             = "the"
    show Head            = "head"
    show Minimum         = "minimum"
    show Maximum         = "maximum"
    show Tail            = "tail"
    show Reverse         = "reverse"
    show And             = "and"
    show Or              = "or"
    show Init            = "init"
    show Last            = "last"
    show Nub             = "nub"
    show Number          = "number"
    show Transpose       = "transpose"
    show (Reshape n)     = printf "reshape(%d)" n
    -- tuple access is pretty-printed in a special way
    show TupElem{}       = $impossible
  
data Prim2 = Group
           | Sort
           | Restrict
           | Append
           | Index
           | Zip
           | Cons
           | CartProduct
           | NestProduct
           | ThetaJoin (L.JoinPredicate L.JoinExpr)
           | NestJoin (L.JoinPredicate L.JoinExpr)
           | SemiJoin (L.JoinPredicate L.JoinExpr)
           | AntiJoin (L.JoinPredicate L.JoinExpr)
           deriving (Eq)

instance Show Prim2 where
    show Group        = "group"
    show Sort         = "sort"
    show Restrict     = "restrict"
    show Append       = "append"
    show Index        = "index"
    show Zip          = "zip"
    show Cons         = "cons"
    show CartProduct  = "⨯"
    show NestProduct  = "▽"
    show (ThetaJoin p) = printf "⨝_%s" (pp p)
    show (NestJoin p)  = printf "△_%s" (pp p)
    show (SemiJoin p)  = printf "⋉_%s" (pp p)
    show (AntiJoin p)  = printf "▷_%s" (pp p)
