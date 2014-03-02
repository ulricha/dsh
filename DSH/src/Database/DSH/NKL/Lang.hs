{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving    #-}

module Database.DSH.NKL.Lang
  ( Expr(..)
  , Typed(..)
  , freeVars
  , Prim1Op(..)
  , Prim2Op(..)
  , Prim1(..)
  , Prim2(..)
  , Column
  , Key
  ) where

import           Text.PrettyPrint.ANSI.Leijen
import           Text.Printf

import           Database.DSH.Common.Data.Op
import           Database.DSH.Common.Data.JoinExpr
import           Database.DSH.Common.Data.Expr
import           Database.DSH.Common.Data.Val(Val())
import           Database.DSH.Common.Data.Type(Type, Typed, typeOf)
  
import qualified Data.Set as S

-- | Nested Kernel Language (NKL) expressions
data Expr  = Table Type String [Column] [Key]
           | App Type Expr Expr
           | AppE1 Type (Prim1 Type) Expr
           | AppE2 Type (Prim2 Type) Expr Expr
           | BinOp Type ScalarBinOp Expr Expr
           | UnOp Type ScalarUnOp Expr
           | Lam Type Ident Expr
           | If Type Expr Expr Expr
           | Const Type Val
           | Var Type Ident

instance Typed Expr where
  typeOf (Table t _ _ _) = t
  typeOf (App t _ _)     = t
  typeOf (AppE1 t _ _)   = t
  typeOf (AppE2 t _ _ _) = t
  typeOf (Lam t _ _)     = t
  typeOf (If t _ _ _)    = t
  typeOf (BinOp t _ _ _) = t
  typeOf (UnOp t _ _)    = t
  typeOf (Const t _)     = t
  typeOf (Var t _)       = t

instance Pretty Expr where
    pretty (Table _ n _ _)    = text "table" <+> text n
    pretty (App _ e1 e2)      = (parenthize e1) <+> (parenthize e2)
    pretty (AppE1 _ p1 e)     = (text $ show p1) <+> (parenthize e)
    pretty (AppE2 _ p1 e1 e2) = (text $ show p1) <+> (align $ (parenthize e1) </> (parenthize e2))
    pretty (BinOp _ o e1 e2)  = (parenthize e1) <+> (text $ show o) <+> (parenthize e2)
    pretty (UnOp _ o e)       = text (show o) <> parens (pretty e)
    pretty (Lam _ v e)        = char '\\' <> text v <+> text "->" <+> pretty e
    pretty (If _ c t e)       = text "if" 
                             <+> pretty c 
                             <+> text "then" 
                             <+> (parenthize t) 
                             <+> text "else" 
                             <+> (parenthize e)
    pretty (Const _ v)        = text $ show v
    pretty (Var _ s)          = text s

parenthize :: Expr -> Doc
parenthize e = 
    case e of
        Var _ _        -> pretty e
        Const _ _      -> pretty e
        Table _ _ _ _  -> pretty e
        _              -> parens $ pretty e

deriving instance Eq Expr
deriving instance Ord Expr

freeVars :: Expr -> S.Set String
freeVars (Table _ _ _ _)   = S.empty
freeVars (App _ e1 e2)     = freeVars e1 `S.union` freeVars e2
freeVars (AppE1 _ _ e1)    = freeVars e1
freeVars (AppE2 _ _ e1 e2) = freeVars e1 `S.union` freeVars e2
freeVars (Lam _ x e)       = (freeVars e) S.\\ S.singleton x
freeVars (If _ e1 e2 e3)   = freeVars e1 `S.union` freeVars e2 `S.union` freeVars e3
freeVars (BinOp _ _ e1 e2) = freeVars e1 `S.union` freeVars e2
freeVars (UnOp _ _ e)      = freeVars e
freeVars (Const _ _)       = S.empty
freeVars (Var _ x)         = S.singleton x

data Prim1Op = Length | Concat 
             | Sum | Avg | The | Fst | Snd 
             | Head | Minimum | Maximum 
             | Tail 
             | Reverse | And | Or 
             | Init | Last | Nub 
             | Number
             | Reshape Integer
             | Transpose
             deriving (Eq, Ord)
             
data Prim1 t = Prim1 Prim1Op t deriving (Eq, Ord)

instance Show Prim1Op where
  show Length          = "length"
  show Concat          = "concat"
  show Sum             = "sum"
  show Avg             = "avg"
  show The             = "the"
  show Fst             = "fst"
  show Snd             = "snd"
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

instance Show (Prim1 t) where
  show (Prim1 o _) = show o

data Prim2Op = Map 
             | GroupWithKey
             | SortWith 
             | Pair
             | Filter 
             | Append
             | Index 
             | Zip
             | CartProduct
             | NestProduct
             | EquiJoin JoinExpr JoinExpr
             | NestJoin JoinExpr JoinExpr
             | SemiJoin JoinExpr JoinExpr
             | AntiJoin JoinExpr JoinExpr
             deriving (Eq, Ord)
             
data Prim2 t = Prim2 Prim2Op t deriving (Eq, Ord)

instance Show Prim2Op where
  show Map          = "map"
  show GroupWithKey = "groupWithKey"
  show SortWith     = "sortWith"
  show Pair         = "pair"
  show Filter       = "filter"
  show Append       = "append"
  show Index        = "index"
  show Zip          = "zip"
  show CartProduct  = "⨯"
  show NestProduct  = "▽"
  show (EquiJoin e1 e2) = printf "⨝ (%s | %s)" (show e1) (show e2)
  show (NestJoin e1 e2) = printf "△ (%s | %s)" (show e1) (show e2)
  show (SemiJoin e1 e2) = printf "⋉ (%s | %s)" (show e1) (show e2)
  show (AntiJoin e1 e2) = printf "▷ (%s | %s)" (show e1) (show e2)
  
instance Show (Prim2 t) where
  show (Prim2 o _) = show o
