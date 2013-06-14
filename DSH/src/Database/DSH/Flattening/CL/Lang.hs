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
  , subst
  , substQuals
  , tuplify
  , tuplifyQuals
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
import           Database.DSH.Flattening.Common.Data.JoinExpr
import           Database.DSH.Flattening.Common.Data.Val(Val())
import           Database.DSH.Flattening.Common.Data.Type
  
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
  
------------------------------------------------------------------------------------------
-- Some utilities for transformations on CL expressions

-- | Compute free variables of a CL expression
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

-- | Substitution: subst v r e ~ e[v/r]
subst :: Ident -> Expr -> Expr -> Expr
subst _ _ table@(Table _ _ _ _) = table
subst v r (App t e1 e2)         = App t (subst v r e1) (subst v r e2)
subst v r (AppE1 t p e)         = AppE1 t p (subst v r e)
subst v r (AppE2 t p e1 e2)     = AppE2 t p (subst v r e1) (subst v r e2)
subst v r (BinOp t o e1 e2)     = BinOp t o (subst v r e1) (subst v r e2)
-- FIXME for the moment, we assume that all lambda variables are unique
-- and we don't need to check for name capturing/do alpha-conversion.
subst v r lam@(Lam t v' e)      = if v' == v
                                     then lam
                                     else Lam t v' (subst v r e)
subst _ _ c@(Const _ _)         = c
subst v r var@(Var _ v')        = if v == v' then r else var
subst v r (If t c thenE elseE)  = If t (subst v r c) (subst v r thenE) (subst v r elseE)
subst v r (Comp t e qs)         = Comp t (subst v r e) (substQuals v r qs)

-- | Substitution on a list of qualifiers
substQuals :: Ident -> Expr -> [Qualifier] -> [Qualifier]
substQuals v r ((GuardQ g) : qs)               = (GuardQ (subst v r g)) : (substQuals v r qs)
substQuals v r ((BindQ v' s) : qs) | v == v'   = (BindQ v' (subst v r s)) : qs
substQuals v r ((BindQ v' s) : qs) | otherwise = (BindQ v' (subst v r s)) : (substQuals v r qs)
substQuals _ _ []                                 = []

-- tuplify v1 v2 e = e[v1/fst v1][v2/snd v1]
tuplify :: (Ident, Type) -> (Ident, Type) -> Expr -> Expr
tuplify (v1, t1) (v2, t2) e = subst v2 v2Rep $ subst v1 v1Rep e

  where (v1Rep, v2Rep) = tupleVars (v1, t1) (v2, t2)

tuplifyQuals :: (Ident, Type) -> (Ident, Type) -> [Qualifier] -> [Qualifier]
tuplifyQuals (v1, t1) (v2, t2) qs = substQuals v2 v2Rep $ substQuals v1 v1Rep qs

  where (v1Rep, v2Rep) = tupleVars (v1, t1) (v2, t2)

tupleVars :: (Ident, Type) -> (Ident, Type) -> (Expr, Expr)
tupleVars (v1, t1) (_, t2) = (v1Rep, v2Rep)
  where v1'    = Var pt v1
        pt     = pairT t1 t2
        v1Rep  = AppE1 t1 (Prim1 Fst (pt .-> t1)) v1'
        v2Rep  = AppE1 t2 (Prim1 Snd (pt .-> t2)) v1'
