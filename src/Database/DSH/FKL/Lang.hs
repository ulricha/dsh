{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}

module Database.DSH.FKL.Lang where

import           Prelude hiding ((<$>))
import           Text.PrettyPrint.ANSI.Leijen
import           Text.Printf

import           Database.DSH.Common.Impossible
import           Database.DSH.Common.Pretty
import           Database.DSH.Common.Nat
import qualified Database.DSH.Common.Lang   as L
import           Database.DSH.Common.Type   (Type, Typed, typeOf)


-- | 'LiftedN' defines an FKL dialect in which primitives and
-- operators might be lifted to arbitrary levels.
data LiftedN = LiftedN Nat deriving (Show)

-- | 'Lifted' defines an FKL dialect in which primitives and operators
-- occur either unlifted or lifted once.
data Lifted = Lifted | NotLifted deriving (Show)

-- | 'FExpr' is the target language of the flattening transformation.
data ExprTempl l e = Table Type String L.BaseTableSchema
                   | PApp1 Type Prim1 l (ExprTempl l e)
                   | PApp2 Type Prim2 l (ExprTempl l e) (ExprTempl l e)
                   | PApp3 Type Prim3 l (ExprTempl l e) (ExprTempl l e) (ExprTempl l e)
                   | If Type (ExprTempl l e) (ExprTempl l e) (ExprTempl l e)
                   | BinOp Type L.ScalarBinOp l (ExprTempl l e) (ExprTempl l e)
                   | UnOp Type L.ScalarUnOp l (ExprTempl l e)
                   | Const Type [L.Val]
                   | Ext e
                   | Let Type L.Ident (ExprTempl l e) (ExprTempl l e)
                   | Var Type L.Ident
                   | MkTuple Type l [ExprTempl l e]

data BroadcastExt = Broadcast Nat Type LExpr LExpr

data ShapeExt = Forget Nat Type FExpr
              | Imprint Nat Type FExpr FExpr

type FExpr = ExprTempl Lifted ShapeExt
type LExpr = ExprTempl LiftedN BroadcastExt

-- | Forget does not unsegment the vector. That is: the descriptor
-- might not be normalized and segment descriptors other than 1 might
-- occur. This is propably ok when we know that a concated vector will
-- be unconcated again. We know this statically when introducing
-- concat/unconcat for higher-lifted primitives.

data Prim1 = Concat
           | TupElem TupleIndex
           | Reverse
           | Nub
           | Number
           | Sort
           | Restrict
           | Group
           | Singleton
           | Only
           | Agg L.AggrFun
           | LitExt L.ScalarVal
    deriving (Show, Eq)

data Prim2 = Append
           | Zip
           | CartProduct
           | ThetaJoin (L.JoinPredicate L.ScalarExpr)
           | NestJoin (L.JoinPredicate L.ScalarExpr)
           | GroupJoin (L.JoinPredicate L.ScalarExpr) (L.NE L.AggrApp)
           | SemiJoin (L.JoinPredicate L.ScalarExpr)
           | AntiJoin (L.JoinPredicate L.ScalarExpr)
           | Dist
           deriving (Show, Eq)

isJoinOp :: Prim2 -> Bool
isJoinOp op =
    case op of
        CartProduct -> True
        ThetaJoin{} -> True
        NestJoin{}  -> True
        GroupJoin{} -> True
        SemiJoin{}  -> True
        AntiJoin{}  -> True
        Append      -> False
        Zip         -> False
        Dist        -> False

data Prim3 = Combine
    deriving (Show, Eq)

instance Typed e => Typed (ExprTempl l e) where
    typeOf (Var t _)           = t
    typeOf (Let t _ _ _)       = t
    typeOf (Table t _ _)       = t
    typeOf (PApp1 t _ _ _)     = t
    typeOf (PApp2 t _ _ _ _)   = t
    typeOf (PApp3 t _ _ _ _ _) = t
    typeOf (If t _ _ _)        = t
    typeOf (BinOp t _ _ _ _)   = t
    typeOf (UnOp t _ _ _)      = t
    typeOf (Const t _)         = t
    typeOf (MkTuple t _ _)     = t
    typeOf (Ext o)             = typeOf o

instance Typed BroadcastExt where
    typeOf (Broadcast _ t _ _) = t

instance Typed ShapeExt where
    typeOf (Forget _ t _)    = t
    typeOf (Imprint _ t _ _) = t

--------------------------------------------------------------------------------
-- Pretty-printing of FKL dialects

superscript :: Int -> Doc
superscript 0 = char '⁰'
superscript 1 = char '¹'
superscript 2 = char '²'
superscript 3 = char '³'
superscript 4 = char '⁴'
superscript 5 = char '⁵'
superscript 6 = char '⁶'
superscript 7 = char '⁷'
superscript 8 = char '⁸'
superscript n = char '^' <> int n

subscript :: Int -> Doc
subscript 1 = char '₁'
subscript 2 = char '₂'
subscript 3 = char '₃'
subscript 4 = char '₄'
subscript 5 = char '₅'
subscript 6 = char '₆'
subscript 7 = char '₇'
subscript 8 = char '₈'
subscript n = char '_' <> int n

instance Pretty Lifted where
    pretty Lifted    = super $ text "¹"
    pretty NotLifted = super $ text "⁰"

instance Pretty LiftedN where
    pretty (LiftedN n)    = super $ superscript (intFromNat n)

instance Pretty Prim1 where
    pretty (LitExt v)   = combinator $ text $ printf "ext{%s}" (pp v)
    pretty Concat       = combinator $ text "concat"
    pretty Reverse      = combinator $ text "reverse"
    pretty Nub          = combinator $ text "nub"
    pretty Number       = combinator $ text "number"
    pretty Sort         = combinator $ text "sort"
    pretty Restrict     = restrict $ text "restrict"
    pretty Group        = combinator $ text "group"
    pretty Singleton    = combinator $ text "sng"
    pretty Only         = combinator $ text "only"
    pretty (Agg a)      = pretty a
    pretty TupElem{}    = $impossible

instance Pretty Prim2 where
    pretty Dist            = dist $ text "dist"
    pretty Append          = combinator $ text "append"
    pretty Zip             = combinator $ text "zip"
    pretty CartProduct     = join $ text "cartproduct"
    pretty (ThetaJoin p)   = join $ text $ printf "thetajoin{%s}" (pp p)
    pretty (NestJoin p)    = join $ text $ printf "nestjoin{%s}" (pp p)
    pretty (GroupJoin p a) = join $ text $ printf "groupjoin{%s, %s}" (pp p) (pp a)
    pretty (SemiJoin p)    = join $ text $ printf "semijoin{%s}" (pp p)
    pretty (AntiJoin p)    = join $ text $ printf "antijoin{%s}" (pp p)

instance Pretty Prim3 where
    pretty Combine = combinator $ text "combine"

instance (Pretty l, Pretty e) => Pretty (ExprTempl l e) where
    pretty (MkTuple _ l es) = prettyTuple (map pretty es) <> pretty l
    pretty (Var _ n) = text n
    pretty (Let _ x e1 e) = prettyLet (text x) (pretty e1) (pretty e)
    pretty (Table _ n _) = kw (text "table") <> parens (text n)
    pretty (PApp1 _ (TupElem n) l e1) =
        parenthize e1 <> dot <> int (tupleIndex n) <> pretty l

    pretty (PApp1 _ f l e1) =
        pretty f <> pretty l <+> parenthize e1

    pretty (PApp2 _ p2 l e1 e2)
        | isJoinOp p2 = prettyJoin (pretty p2 <> pretty l)
                                   (parenthize e1)
                                   (parenthize e2)
        | otherwise   = prettyApp2 (pretty p2 <> pretty l)
                                   (parenthize e1)
                                   (parenthize e2)

    pretty (PApp3 _ f l e1 e2 e3) =
        pretty f <> pretty l
        <+> align (parenthize e1 </> parenthize e2 </> parenthize e3)
    pretty (If _ e1 e2 e3) =
        let e1' = pretty e1
            e2' = pretty e2
            e3' = pretty e3
        in text "if" <+> e1'
           </> nest 2 (text "then" <+> e2')
           </> nest 2 (text "else" <+> e3')

    pretty (BinOp _ o l e1 e2)
        | L.isBinInfixOp o = prettyInfixBinOp (pretty o <> pretty l)
                                              (parenthize e1)
                                              (parenthize e2)
        | otherwise        = prettyPrefixBinOp (pretty o <> pretty l)
                                               (parenthize e1)
                                               (parenthize e2)

    pretty (UnOp _ o l e) = prettyUnOp (pretty o <> pretty l) (pretty e)

    pretty (Const _ v) = pretty v

    pretty (Ext o) = pretty o

instance Pretty ShapeExt where
    pretty (Forget n _ e) =
        forget (text "forget")
        <> forget (subscript $ intFromNat n)
        <+> parenthize e

    pretty (Imprint n _ e1 e2) =
        prettyApp2 (forget (text "imprint") <> forget (subscript $ intFromNat n))
                   (parenthize e1)
                   (parenthize e2)

instance Pretty BroadcastExt where
    pretty (Broadcast n _ e1 e2) =
        prettyApp2 (forget (text "broadcast") <> forget (subscript $ intFromNat n))
                   (parenthize e1)
                   (parenthize e2)

parenthize :: (Pretty l, Pretty e) => ExprTempl l e -> Doc
parenthize e =
    case e of
        Const{}                 -> pretty e
        Table{}                 -> pretty e
        Var{}                   -> pretty e
        PApp1 _ (TupElem _) _ _ -> pretty e
        _                       -> parens $ pretty e

