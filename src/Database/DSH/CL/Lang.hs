{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TemplateHaskell       #-}

module Database.DSH.CL.Lang
    ( module Database.DSH.Common.Type
    , Expr(..)
    , NL(..), reverseNL, toList, fromList, fromListSafe, appendNL, toNonEmpty
    , Qual(..), isGuard, isBind
    , Typed(..)
    , Prim1(..)
    , Prim2(..)
    ) where

import qualified Data.Foldable                  as F
import           Data.List.NonEmpty             (NonEmpty ((:|)))
import qualified Data.Traversable               as T

import           Text.PrettyPrint.ANSI.Leijen   hiding ((<$>))
import           Text.Printf

import           Database.DSH.Common.Impossible
import qualified Database.DSH.Common.Lang       as L
import           Database.DSH.Common.Nat
import           Database.DSH.Common.Pretty
import           Database.DSH.Common.Type

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

data Prim1 = Singleton
           | Only
           | Length
           | Concat
           | Null
           | Sum
           | Avg
           | Minimum
           | Maximum
           | Reverse
           | And
           | Or
           | Nub
           | Number
           | Sort
           | Group
           | Guard
           | TupElem TupleIndex
           deriving (Eq, Show)

instance Pretty Prim1 where
  pretty Sort            = combinator $ text "sort"
  pretty Group           = combinator $ text "group"
  pretty Singleton       = combinator $ text "sng"
  pretty Only            = combinator $ text "only"
  pretty Length          = combinator $ text "length"
  pretty Concat          = combinator $ text "concat"
  pretty Null            = combinator $ text "null"
  pretty Sum             = combinator $ text "sum"
  pretty Avg             = combinator $ text "avg"
  pretty Minimum         = combinator $ text "minimum"
  pretty Maximum         = combinator $ text "maximum"
  pretty Reverse         = combinator $ text "reverse"
  pretty And             = combinator $ text "and"
  pretty Or              = combinator $ text "or"
  pretty Nub             = combinator $ text "nub"
  pretty Number          = combinator $ text "number"
  pretty Guard           = combinator $ text "guard"
  -- tuple access is pretty-printed in a special way
  pretty TupElem{}       = $impossible

data Prim2 = Append
           | Zip
           | CartProduct
           | NestProduct
           | ThetaJoin (L.JoinPredicate L.JoinExpr)
           | NestJoin (L.JoinPredicate L.JoinExpr)
           | SemiJoin (L.JoinPredicate L.JoinExpr)
           | AntiJoin (L.JoinPredicate L.JoinExpr)
           deriving (Eq, Show)

instance Pretty Prim2 where
  pretty Append        = combinator $ text "append"
  pretty Zip           = combinator $ text "zip"
  pretty CartProduct   = join $ text "cartproduct"
  pretty NestProduct   = join $ text "nestproduct"
  pretty (ThetaJoin p) = join $ text $ printf "thetajoin{%s}" (pp p)
  pretty (NestJoin p)  = join $ text $ printf "nestjoin{%s}" (pp p)
  pretty (SemiJoin p)  = join $ text $ printf "semijoin{%s}" (pp p)
  pretty (AntiJoin p)  = join $ text $ printf "antijoin{%s}" (pp p)

--------------------------------------------------------------------------------
-- CL expressions

data Qual = BindQ L.Ident Expr
          | GuardQ Expr
          deriving (Eq, Show)

isGuard :: Qual -> Bool
isGuard (GuardQ _)   = True
isGuard (BindQ _ _)  = False

isBind :: Qual -> Bool
isBind (GuardQ _)   = False
isBind (BindQ _ _)  = True

data Expr  = Table Type String L.BaseTableSchema
           | AppE1 Type Prim1 Expr
           | AppE2 Type Prim2 Expr Expr
           | BinOp Type L.ScalarBinOp Expr Expr
           | UnOp Type L.ScalarUnOp Expr
           | If Type Expr Expr Expr
           | Lit Type L.Val
           | Var Type L.Ident
           | Comp Type Expr (NL Qual)
           | MkTuple Type [Expr]
           | Let Type L.Ident Expr Expr
           deriving (Show)

instance Pretty Expr where
    pretty (AppE1 _ (TupElem n) e1) =
        parenthize e1 <> dot <> int (tupleIndex n)
    pretty (MkTuple _ es)     = tupled $ map pretty es
    pretty (Table _ n _)      = kw (text "table") <> parens (text n)
    pretty (AppE1 _ p1 e)     = pretty p1 <+> (parenthize e)
    pretty (AppE2 _ p2 e1 e2) = pretty p2
                                <+>
                                (align $ (parenthize e1) </> (parenthize e2))
    pretty (BinOp _ o e1 e2)  = (parenthize e1) <+> (pretty o) <+> (parenthize e2)
    pretty (UnOp _ o e)       = pretty o <> parens (pretty e)
    pretty (If _ c t e)       = kw (text "if")
                                <+> pretty c
                                <+> kw (text "then")
                                <+> (parenthize t)
                                <+> kw (text "else")
                                <+> (parenthize e)
    pretty (Lit _ v)          = pretty v
    pretty (Var _ s)          = text s
    pretty (Comp _ e qs)      = prettyComp (pretty e) (map pretty $ toList qs)

    -- pretty (Comp _ e qs) = encloseSep (comp lbracket) (comp rbracket) empty docs
    --   where
    --     docs = (char ' ' <> pretty e <> char ' ') : qsDocs
    --     qsDocs = case qs of
    --                  q :* qs' -> (comp (char '|') <+> pretty q)
    --                              : [ comp (char ',') <+> pretty q' | q' <- toList qs' ]

    --                  S q      -> [ comp (char '|') <+> pretty q]
    pretty (Let _ x e1 e)     =
        align $ kw (text "let") <+> text x <+> kw (char '=') <+> pretty e1
                </>
                kw (text "in") <+> pretty e

parenthize :: Expr -> Doc
parenthize e =
    case e of
        Var _ _               -> pretty e
        Lit _ _               -> pretty e
        Table _ _ _           -> pretty e
        Comp _ _ _            -> pretty e
        AppE1 _ (TupElem _) _ -> pretty e
        _                     -> parens $ pretty e

instance Pretty Qual where
    pretty (BindQ i e) = text i <+> comp (text "<-") <+> pretty e
    pretty (GuardQ e)  = pretty e

-- -- Binary relational operators are pretty-printed different from other
-- -- combinators
-- isRelOp :: Prim2 -> Bool
-- isRelOp o =
--     case o of
--         ThetaJoin _  -> True
--         NestJoin _   -> True
--         SemiJoin _   -> True
--         AntiJoin _   -> True
--         _            -> False



deriving instance Eq Expr

instance Typed Expr where
    typeOf (Table t _ _)   = t
    typeOf (AppE1 t _ _)   = t
    typeOf (AppE2 t _ _ _) = t
    typeOf (If t _ _ _)    = t
    typeOf (BinOp t _ _ _) = t
    typeOf (UnOp t _ _)    = t
    typeOf (Lit t _)       = t
    typeOf (Var t _)       = t
    typeOf (Comp t _ _)    = t
    typeOf (MkTuple t _)   = t
    typeOf (Let t _ _ _)   = t
