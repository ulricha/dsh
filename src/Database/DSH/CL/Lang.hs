{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE PatternSynonyms       #-}

module Database.DSH.CL.Lang
    ( module Database.DSH.Common.Type
    , Expr(..)
    , NL(..), reverseNL, toList, fromList, fromListSafe, appendNL, toNonEmpty
    , Qual(..), isGuard, isBind
    , Typed(..)
    , Prim1Op(..)
    , Prim2Op(..)
    , Prim1(..)
    , Prim2(..)
    ) where

import           Control.Applicative          hiding (empty)

import qualified Data.Foldable                as F
import qualified Data.Traversable             as T
import           Data.List.NonEmpty           (NonEmpty((:|)))

import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import           Text.Printf

import qualified Database.DSH.Common.Lang     as L
import           Database.DSH.Common.Type
import           Database.DSH.Common.Pretty
import           Database.DSH.Impossible

--------------------------------------------------------------------------------
-- A simple type of nonempty lists, used for comprehension
-- qualifiers. This type is used instead of Data.List.NonEmpty to have
-- a proper list spine for which Kure traversals can be defined
-- easily.

data NL a = a :* (NL a)
          | S a
          deriving (Eq, Ord)

infixr :*

instance Show a => Show (NL a) where
    show = show . toList

instance Pretty a => Pretty (NL a) where
    pretty = pretty . toList

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

fromList :: [a] -> Maybe (NL a)
fromList [] = Nothing
fromList as = Just $ aux as
  where
    aux :: [a] -> NL a
    aux (x : []) = S x
    aux (x : xs) = x :* aux xs
    aux []       = $impossible

fromListSafe :: a -> [a] -> NL a
fromListSafe a [a1]      = a :* S a1
fromListSafe a []        = S a
fromListSafe a (a1 : as) = a :* fromListSafe a1 as

toNonEmpty :: NL a -> NonEmpty a
toNonEmpty (a :* as) = a :| toList as
toNonEmpty (S a)     = a :| []

reverseNL :: NL a -> NL a
reverseNL (a :* as) = F.foldl (flip (:*)) (S a) as
reverseNL (S a)     = S a

appendNL :: NL a -> NL a -> NL a
appendNL (a :* as) bs = a :* appendNL as bs
appendNL (S a)     bs = a :* bs

--------------------------------------------------------------------------------
-- CL primitives

data Prim1Op = Length 
             | Concat
             | Null
             | Sum 
             | Avg 
             | The 
             | Fst 
             | Snd
             | Head 
             | Minimum 
             | Maximum
             | Tail
             | Reverse 
             | And | Or
             | Init 
             | Last 
             | Nub
             | Number 
             | Guard
             | Reshape Integer
             | Transpose
             deriving (Eq, Ord)

data Prim1 t = Prim1 Prim1Op t deriving (Eq, Ord)

instance Show Prim1Op where
  show Length          = "length"
  show Concat          = "concat"
  show Null            = "null"
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
  show Guard           = "guard"
  show Transpose       = "transpose"
  show (Reshape n)     = printf "reshape(%d)" n

instance Show (Prim1 t) where
  show (Prim1 o _) = show o

data Prim2Op = Map 
             | ConcatMap 
             | GroupWithKey
             | SortWith 
             | Pair
             | Filter 
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
             deriving (Eq, Ord)

data Prim2 t = Prim2 Prim2Op t deriving (Eq, Ord)

instance Show Prim2Op where
  show Map          = "map"
  show ConcatMap    = "concatMap"
  show GroupWithKey = "groupWithKey"
  show SortWith     = "sortWith"
  show Pair         = "pair"
  show Filter       = "filter"
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

instance Show (Prim2 t) where
  show (Prim2 o _) = show o

--------------------------------------------------------------------------------
-- CL expressions

data Qual = BindQ L.Ident Expr
          | GuardQ Expr
          deriving (Eq, Ord, Show)

isGuard :: Qual -> Bool
isGuard (GuardQ _)   = True
isGuard (BindQ _ _)  = False

isBind :: Qual -> Bool
isBind (GuardQ _)   = False
isBind (BindQ _ _)  = True

data Expr  = Table Type String [L.Column] L.TableHints
           | App Type Expr Expr
           | AppE1 Type (Prim1 Type) Expr
           | AppE2 Type (Prim2 Type) Expr Expr
           | BinOp Type L.ScalarBinOp Expr Expr
           | UnOp Type L.ScalarUnOp Expr
           | Lam Type L.Ident Expr
           | If Type Expr Expr Expr
           | Lit Type L.Val
           | Var Type L.Ident
           | Comp Type Expr (NL Qual)
           deriving (Show)


instance Pretty Expr where
    pretty (Table _ n _ _)    = text "table" <+> text n
    pretty (App _ e1 e2)      = (parenthize e1) <+> (parenthize e2)
    pretty (AppE1 _ p1 e)     = (text $ show p1) <+> (parenthize e)
    pretty (AppE2 _ p1 e1@(Comp _ _ _) e2) = (text $ show p1) <+> (align $ (parenthize e1) PP.<$> (parenthize e2))
    pretty (AppE2 _ p1 e1 e2@(Comp _ _ _)) = (text $ show p1) <+> (align $ (parenthize e1) PP.<$> (parenthize e2))
    pretty (AppE2 _ p1 e1 e2) | isRelOp p1 = (text $ show p1) <$$> (indent 4 $ parenthize e1 <$$> parenthize e2)
    pretty (AppE2 _ p1 e1 e2) = (text $ show p1) <+> (align $ (parenthize e1) </> (parenthize e2))
    pretty (BinOp _ o e1 e2)  = (parenthize e1) <+> (pretty o) <+> (parenthize e2)
    pretty (UnOp _ o e)       = pretty o <> parens (pretty e)
    pretty (Lam _ v e)        = char '\\' <> text v <+> text "->" <+> pretty e
    pretty (If _ c t e)       = text "if"
                             <+> pretty c
                             <+> text "then"
                             <+> (parenthize t)
                             <+> text "else"
                             <+> (parenthize e)
    pretty (Lit _ v)          = text $ show v
    pretty (Var _ s)          = text s

    pretty (Comp _ e qs) = encloseSep lbracket rbracket empty docs
                         where docs = (char ' ' <> pretty e <> char ' ') : qsDocs
                               qsDocs =
                                 case qs of
                                   q :* qs' -> (char '|' <+> pretty q)
                                               : [ char ',' <+> pretty q' | q' <- toList qs' ]

                                   S q      -> [char '|' <+> pretty q]

parenthize :: Expr -> Doc
parenthize e =
    case e of
        Var _ _        -> pretty e
        Lit _ _        -> pretty e
        Table _ _ _ _  -> pretty e
        Comp _ _ _     -> pretty e
        _              -> parens $ pretty e

instance Pretty Qual where
    pretty (BindQ i e) = text i <+> text "<-" <+> pretty e
    pretty (GuardQ e)  = pretty e

-- Binary relational operators are pretty-printed different from other
-- combinators
isRelOp :: Prim2 t -> Bool
isRelOp o =
    case o of
        Prim2 (ThetaJoin _) _  -> True
        Prim2 (NestJoin _) _   -> True
        Prim2 (SemiJoin _) _   -> True
        Prim2 (AntiJoin _) _   -> True
        _                      -> False



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
  typeOf (UnOp t _ _)    = t
  typeOf (Lit t _)       = t
  typeOf (Var t _)       = t
  typeOf (Comp t _ _)    = t


