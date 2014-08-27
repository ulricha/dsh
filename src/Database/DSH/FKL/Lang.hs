{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE StandaloneDeriving #-}

module Database.DSH.FKL.Lang where

import           Text.PrettyPrint.ANSI.Leijen
import           Text.Printf

import           Database.DSH.Common.Pretty
import qualified Database.DSH.Common.Lang   as L
import           Database.DSH.Common.Type   (Type, Typed, typeOf)

import           GHC.Generics               (Generic)

---------------------------------------------------------------------------------
-- Natural numbers that encode lifting levels

data Nat = Zero | Succ Nat

intFromNat :: Nat -> Int
intFromNat Zero     = 0
intFromNat (Succ n) = 1 + intFromNat n

-- | 'LiftedN' defines an FKL dialect in which primitives and
-- operators might be lifted to arbitrary levels.
data LiftedN p = LiftedN Nat p

-- | 'Lifted' defines an FKL dialect in which primitives and operators
-- occur either unlifted or lifted once.
data Lifted p = Lifted p
              | NotLifted p
              deriving (Show)

-- | 'LExpr' serves as an intermediate language during flattening. It
-- features no comprehensions but the dist combinator and primitive
-- combinators and operators that can occur arbitrarily
-- lifted. Variables might still be present.
data LExpr = LTable   Type String [L.Column] L.TableHints
           | LPApp1   Type (LiftedN Prim1) LExpr
           | LPApp2   Type (LiftedN Prim2) LExpr LExpr
           | LPApp3   Type (LiftedN Prim3) LExpr LExpr LExpr
           | LIf      Type LExpr LExpr LExpr
           | LBinOp   Type (LiftedN L.ScalarBinOp) LExpr LExpr
           | LUnOp    Type (LiftedN L.ScalarUnOp) LExpr
           | LConst   Type L.Val
           | LVar     Type L.Ident

-- | 'Expr' is the final target language of the flattening
-- transformation. Primitive combinators and operators are only lifted
-- once. To achieve that, we introduce the 'unconcat' and
-- '(quick)Concat' combinators to temporarily flatten nested
-- structures. Note that variables can no longer occur, as
-- Prins/Palmer-style flattening implicitly inlines all generator
-- expressions.
data Expr = Table   Type String [L.Column] L.TableHints
          | PApp1   Type (Lifted Prim1) Expr
          | PApp2   Type (Lifted Prim2) Expr Expr
          | PApp3   Type (Lifted Prim3) Expr Expr Expr
          | If      Type Expr Expr Expr
          | BinOp   Type (Lifted L.ScalarBinOp) Expr Expr
          | UnOp    Type (Lifted L.ScalarUnOp) Expr
          | Const   Type L.Val
          | QuickConcat Type Expr
          | UnConcat Int Type Expr Expr

-- | QuickConcat does not unsegment the vector. That is:
-- the descriptor might not be normalized and segment
-- descriptors other than 1 might occur. This is propably
-- ok when we know that a concated vector will be
-- unconcated again. We know this statically when
-- introducing concat/unconcat for higher-lifted
-- primitives.

data Prim1 = Length
           | Concat
           | Fst
           | Snd
           | Sum
           | Avg
           | Minimum
           | Maximum
           | The
           | Tail
           | Reverse
           | And
           | Or
           | Init
           | Last
           | Nub
           | Number
           | Transpose
           | Reshape Integer
    deriving (Show, Eq, Generic)

data Prim2 = Group
           | Sort
           | Restrict
           | Pair
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
           | Dist
           deriving (Show, Eq, Generic)

data Prim3 = Combine
    deriving (Show, Eq, Generic)

instance Typed LExpr where
    typeOf (LTable t _ _ _)    = t
    typeOf (LPApp1 t _ _)      = t
    typeOf (LPApp2 t _ _ _)    = t
    typeOf (LPApp3 t _ _ _ _)  = t
    typeOf (LIf t _ _ _)       = t
    typeOf (LBinOp t _ _ _)    = t
    typeOf (LUnOp t _ _)       = t
    typeOf (LConst t _)        = t
    typeOf (LVar t _)          = t

instance Typed Expr where
    typeOf (Table t _ _ _)    = t
    typeOf (PApp1 t _ _)      = t
    typeOf (PApp2 t _ _ _)    = t
    typeOf (PApp3 t _ _ _ _)  = t
    typeOf (If t _ _ _)       = t
    typeOf (BinOp t _ _ _)    = t
    typeOf (UnOp t _ _)       = t
    typeOf (Const t _)        = t
    typeOf (QuickConcat t _)  = t
    typeOf (UnConcat _ t _ _) = t

--------------------------------------------------------------------------------
-- Pretty-printing of FKL dialects

superscript :: Int -> Doc
superscript 1 = char '¹'
superscript 2 = char '²'
superscript 3 = char '³'
superscript 4 = char '⁴'
superscript 5 = char '⁵'
superscript 6 = char '⁶'
superscript n = char '^' <> int n

instance Pretty p => Pretty (Lifted p) where
    pretty (Lifted p)    = pretty p <> text "ᴸ"
    pretty (NotLifted p) = pretty p

instance Pretty p => Pretty (LiftedN p) where
    pretty (LiftedN Zero p) = pretty p
    pretty (LiftedN n p)    = pretty p <> superscript (intFromNat n)

instance Pretty Prim1 where
    pretty Length       = text "length"
    pretty Fst          = text "fst"
    pretty Snd          = text "snd"
    pretty Concat       = text "concat"
    pretty Sum          = text "sum"
    pretty Avg          = text "avg"
    pretty The          = text "the"
    pretty Minimum      = text "minimum"
    pretty Maximum      = text "maximum"
    pretty Tail         = text "tail"
    pretty Reverse      = text "reverse"
    pretty And          = text "and"
    pretty Or           = text "or"
    pretty Init         = text "init"
    pretty Last         = text "last"
    pretty Nub          = text "nub"
    pretty Number       = text "number"
    pretty Transpose    = text "transpose"
    pretty (Reshape n)  = text $ printf "reshape(%d)" n

instance Pretty Prim2 where
    pretty Group           = text "group"
    pretty Sort            = text "sort"
    pretty Dist            = text "dist"
    pretty Restrict        = text "restrict"
    pretty Pair            = text "pair"
    pretty Append          = text "append"
    pretty Index           = text "index"
    pretty Zip             = text "zip"
    pretty Cons            = text "cons"
    pretty CartProduct     = text "⨯"
    pretty NestProduct     = text "▽"
    pretty (ThetaJoin p)   = text $ printf "⨝_%s" (pp p)
    pretty (NestJoin p)    = text $ printf "△_%s" (pp p)
    pretty (SemiJoin p)    = text $ printf "⋉_%s" (pp p)
    pretty (AntiJoin p)    = text $ printf "▷_%s" (pp p)

instance Pretty Prim3 where
    pretty Combine = text "combine"

instance Pretty LExpr where
    pretty (LTable _ n _c _k) = text "table" <> parens (text n)

    pretty (LPApp1 _ f e1) =
        pretty f <+> (parenthizeL e1)

    pretty (LPApp2 _ f e1 e2) =
        pretty f <+> (align $ (parenthizeL e1) <$> (parenthizeL e2))

    pretty (LPApp3 _ f e1 e2 e3) =
        pretty f 
        <+> (align $ (parenthizeL e1) 
                     <$> (parenthizeL e2) 
                     <$> (parenthizeL e3))

    pretty (LIf _ e1 e2 e3) =
        let e1' = pretty e1
            e2' = pretty e2
            e3' = pretty e3
        in text "if" <+> e1'
           </> (nest 2 $ text "then" <+> e2')
           </> (nest 2 $ text "else" <+> e3')

    pretty (LBinOp _ o e1 e2) =
        parenthizeL e1 <+> pretty o <+> parenthizeL e2

    pretty (LUnOp _ o e) =
        pretty o <> parenthizeL e

    pretty (LConst _ v) =
        pretty v

    pretty (LVar _ x) =
        text x

parenthizeL :: LExpr -> Doc
parenthizeL e = 
    case e of
        LTable {} -> pretty e
        LConst {} -> pretty e
        LVar {}   -> pretty e
        _        -> parens $ pretty e

instance Pretty Expr where
    pretty (Table _ n _c _k) = text "table" <> parens (text n)

    pretty (PApp1 _ f e1) =
        pretty f <+> (parenthizeE e1)

    pretty (PApp2 _ f e1 e2) =
        pretty f <+> (align $ (parenthizeE e1) <$> (parenthizeE e2))

    pretty (PApp3 _ f e1 e2 e3) =
        pretty f 
        <+> (align $ (parenthizeE e1) 
                     <$> (parenthizeE e2) 
                     <$> (parenthizeE e3))

    pretty (If _ e1 e2 e3) =
        let e1' = pretty e1
            e2' = pretty e2
            e3' = pretty e3
        in text "if" <+> e1'
           </> (nest 2 $ text "then" <+> e2')
           </> (nest 2 $ text "else" <+> e3')

    pretty (BinOp _ o e1 e2) =
        let e1' = pretty e1
            e2' = pretty e2
        in parens $ e1' <+> pretty o <+> e2'

    pretty (UnOp _ o e) =
        pretty o <> parens (pretty e)

    pretty (Const _ v) =
        pretty v

    pretty (QuickConcat _ e) = text "quickConcat" <+> (parenthizeE e)

    pretty (UnConcat n _ e1 e2) = 
        text "unconcat" 
        <> (angles $ int n) 
        <+> (align $ (parenthizeE e1) 
                     <$> (parenthizeE e2))

parenthizeE :: Expr -> Doc
parenthizeE e =
    case e of
        Const{} -> pretty e
        Table{} -> pretty e
        _       -> parens $ pretty e
