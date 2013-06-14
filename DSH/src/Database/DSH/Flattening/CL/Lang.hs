{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE DeriveDataTypeable    #-}

module Database.DSH.Flattening.CL.Lang
  ( Expr(..)
  , Qualifier(..)
  , Typed(..)
  , freeVars
  , Prim1Op(..)
  , Prim2Op(..)
  , Prim1(..)
  , Prim2(..)
  , Column
  , Key
  ) where

import           Data.Data

import           Text.PrettyPrint.HughesPJ

import           Database.DSH.Flattening.Common.Data.Op
import           Database.DSH.Flattening.Common.Data.Expr
import           Database.DSH.Flattening.Common.Data.Val(Val())
import           Database.DSH.Flattening.Common.Data.Type(Type, Typed, typeOf)
  
import qualified Data.Set as S

data Prim1Op = Length |  Not |  Concat 
             | Sum | Avg | The | Fst | Snd 
             | Head | Minimum | Maximum 
             | IntegerToDouble | Tail 
             | Reverse | And | Or 
             | Init | Last | Nub 
             | Number | Guard
             deriving (Eq, Ord, Data, Typeable)
             
data Prim1 t = Prim1 Prim1Op t deriving (Eq, Ord, Data, Typeable)

instance Show Prim1Op where
  show Length          = "length"
  show Not             = "not"
  show Concat          = "concat"
  show Sum             = "sum"
  show Avg             = "avg"
  show The             = "the"
  show Fst             = "fst"
  show Snd             = "snd"
  show Head            = "head"
  show Minimum         = "minimum"
  show Maximum         = "maximum"
  show IntegerToDouble = "integerToDouble"
  show Tail            = "tail"
  show Reverse         = "reverse"
  show And             = "and"
  show Or              = "or"
  show Init            = "init"
  show Last            = "last"
  show Nub             = "nub"
  show Number          = "number"
  show Guard           = "guard"
  
instance Show (Prim1 t) where
  show (Prim1 o _) = show o

data Prim2Op = Map | ConcatMap | GroupWithKey
             | SortWith | Pair
             | Filter | Append
             | Index | Take
             | Drop | Zip
             | TakeWhile
             | DropWhile
             | CartProduct
             deriving (Eq, Ord, Data, Typeable)
             
data Prim2 t = Prim2 Prim2Op t deriving (Eq, Ord, Data, Typeable)

instance Show Prim2Op where
  show Map          = "map"
  show ConcatMap    = "concatMap"
  show GroupWithKey = "groupWithKey"
  show SortWith     = "sortWith"
  show Pair         = "pair"
  show Filter       = "filter"
  show Append       = "append"
  show Index        = "index"
  show Take         = "take"
  show Drop         = "drop"
  show Zip          = "zip"
  show TakeWhile    = "takeWhile"
  show DropWhile    = "dropWhile"
  show CartProduct  = "cartProduct"
  
instance Show (Prim2 t) where
  show (Prim2 o _) = show o

data Expr  = Table Type String [Column] [Key] 
           | App Type Expr Expr              
           | AppE1 Type (Prim1 Type) Expr   
           | AppE2 Type (Prim2 Type) Expr Expr 
           | BinOp Type Oper Expr Expr        
           | Lam Type Ident Expr              
           | If Type Expr Expr Expr
           | Const Type Val
           | Var Type Ident
           | Comp Type Expr [Qualifier]
           deriving (Data, Typeable)
           
data Qualifier = BindQ Ident Expr
               | GuardQ Expr
               deriving (Eq, Ord, Data, Typeable)

instance Show Expr where
  show e = render $ pp e
  
ppQualifier :: Qualifier -> Doc
ppQualifier (BindQ i e) = text i <+> text "<-" <+> pp e
ppQualifier (GuardQ e)  = pp e
  
pp :: Expr -> Doc
pp (Table _ n _ _)    = text "table" <+> text n
pp (App _ e1 e2)      = (parens $ pp e1) <+> (parens $ pp e2)
pp (AppE1 _ p1 e)     = (text $ show p1) <+> (parens $ pp e)
pp (AppE2 _ p1 e1 e2) = (text $ show p1) <+> (parens $ pp e1) <+> (parens $ pp e2)
pp (BinOp _ o e1 e2)  = (parens $ pp e1) <+> (text $ show o) <+> (parens $ pp e2)
pp (Lam _ v e)        = char '\\' <> text v <+> text "->" <+> pp e
pp (If _ c t e)       = text "if" <+> pp c <+> text "then" <+> (parens $ pp t) <+> text "else" <+> (parens $ pp e)
pp (Const _ v)        = text $ show v
pp (Var _ s)          = text s
pp (Comp _ e qs)      = brackets $ pp e <+> char '|' <+> (hsep $ punctuate comma $ map ppQualifier qs)

deriving instance Eq Expr
deriving instance Ord Expr

instance Typed Expr where
  typeOf (Table t _ _ _) = t
  typeOf (App t _ _)     = t
  typeOf (AppE1 t _ _)   = t
  typeOf (AppE2 t _ _ _) = t
  typeOf (Lam t _ _)     = t
  typeOf (If t _ _ _)    = t
  typeOf (BinOp t _ _ _) = t
  typeOf (Const t _)     = t
  typeOf (Var t _)       = t
  typeOf (Comp t _ _)    = t

freeVars :: Expr -> S.Set String
freeVars (Table _ _ _ _) = S.empty
freeVars (App _ e1 e2)     = freeVars e1 `S.union` freeVars e2
freeVars (AppE1 _ _ e1)    = freeVars e1
freeVars (AppE2 _ _ e1 e2) = freeVars e1 `S.union` freeVars e2
freeVars (Lam _ x e)       = (freeVars e) S.\\ S.singleton x
freeVars (If _ e1 e2 e3)   = freeVars e1 `S.union` freeVars e2 `S.union` freeVars e3
freeVars (BinOp _ _ e1 e2) = freeVars e1 `S.union` freeVars e2
freeVars (Const _ _)       = S.empty
freeVars (Var _ x)         = S.singleton x
freeVars (Comp _ b qs)     = foldr collect (freeVars b) qs

  where collect (BindQ v e) fvs = S.difference (S.union fvs (freeVars e)) (S.singleton v)
        collect (GuardQ e)  fvs = S.union fvs (freeVars e)
