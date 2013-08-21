{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE DeriveDataTypeable    #-}

module Database.DSH.CL.Lang
  ( module Database.DSH.Common.Data.Op
  , module Database.DSH.Common.Data.Expr
  , module Database.DSH.Common.Data.JoinExpr
  , module Database.DSH.Common.Data.Val
  , module Database.DSH.Common.Data.Type
  , Expr(..)
  , NL(..), reverseNL, toList
  , Qual(..)
  , Typed(..)
  , Prim1Op(..)
  , Prim2Op(..)
  , Prim1(..)
  , Prim2(..)
  ) where

import           Data.Data
                 
import           Control.Applicative
                 
import qualified Data.Foldable as F
import qualified Data.Traversable as T

import           Text.PrettyPrint.HughesPJ
import           Text.Printf

import           Database.DSH.Common.Data.Op
import           Database.DSH.Common.Data.Expr
import           Database.DSH.Common.Data.JoinExpr
import           Database.DSH.Common.Data.Val(Val())
import           Database.DSH.Common.Data.Type
  
import qualified Data.Set as S

--------------------------------------------------------------------------------
-- A simple type of nonempty lists, used for comprehension qualifiers

data NL a = a :* (NL a)
          | S a
          deriving (Data, Typeable, Eq, Ord)
          
infixr :*
          
instance Show a => Show (NL a) where
    show = show . toList 
          
instance Functor NL where
    fmap f (a :* as) = (f a) :* (fmap f as)
    fmap f (S a)     = S (f a)
    
instance F.Foldable NL where
    foldr f z (a :* as) = f a (F.foldr f z as)
    foldr f z (S a)     = f a z
    
instance T.Traversable NL where
    traverse f (a :* as) = (:*) <$> (f a) <*> (T.traverse f as)
    traverse f (S a)     = S <$> (f a)
    
toList :: NL a -> [a]
toList (a :* as) = a : toList as
toList (S a)     = [a]

reverseNL :: NL a -> NL a
reverseNL (a :* as) = F.foldl (flip (:*)) (S a) as
reverseNL (S a)     = S a

--------------------------------------------------------------------------------
-- CL primitives

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
             | EquiJoin JoinExpr JoinExpr
             | NestJoin JoinExpr JoinExpr
             | SemiJoin JoinExpr JoinExpr
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
  show (EquiJoin e1 e2) = printf "\x2a1d (%s, %s)" (show e1) (show e2)
  show (NestJoin e1 e2) = printf "\x25b3 (%s, %s)" (show e1) (show e2)
  show (SemiJoin e1 e2) = printf "\x22c9 (%s, %s)" (show e1) (show e2)
  
instance Show (Prim2 t) where
  show (Prim2 o _) = show o

--------------------------------------------------------------------------------
-- CL expressions

data Qual = BindQ Ident Expr
          | GuardQ Expr
          deriving (Eq, Ord, Data, Typeable)

data Expr  = Table Type String [Column] [Key] 
           | App Type Expr Expr              
           | AppE1 Type (Prim1 Type) Expr   
           | AppE2 Type (Prim2 Type) Expr Expr 
           | BinOp Type Oper Expr Expr        
           | Lam Type Ident Expr              
           | If Type Expr Expr Expr
           | Lit Type Val
           | Var Type Ident
           | Comp Type Expr (NL Qual)
           deriving (Data, Typeable)
           
instance Show Expr where
  show e = render $ pp e
  
ppQual :: Qual -> Doc
ppQual (BindQ i e) = text i <+> text "<-" <+> pp e
ppQual (GuardQ e)  = pp e
  
pp :: Expr -> Doc
pp (Table _ n _ _)    = text "table" <+> text n
pp (App _ e1 e2)      = (parens $ pp e1) <+> (parens $ pp e2)
pp (AppE1 _ p1 e)     = (text $ show p1) <+> (parens $ pp e)
pp (AppE2 _ p1 e1 e2) = (text $ show p1) <+> (parens $ pp e1) <+> (parens $ pp e2)
pp (BinOp _ o e1 e2)  = (parens $ pp e1) <+> (text $ show o) <+> (parens $ pp e2)
pp (Lam _ v e)        = char '\\' <> text v <+> text "->" <+> pp e
pp (If _ c t e)       = text "if" 
                         <+> pp c 
                         <+> text "then" 
                         <+> (parens $ pp t) 
                         <+> text "else" 
                         <+> (parens $ pp e)
pp (Lit _ v)          = text $ show v
pp (Var _ s)          = text s
pp (Comp _ e qs)      = brackets $ char ' ' 
                                   <> pp e 
                                   <+> char '|' 
                                   <+> (hsep $ punctuate comma $ map ppQual $ toList qs)

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
  typeOf (Lit t _)       = t
  typeOf (Var t _)       = t
  typeOf (Comp t _ _)    = t
  

