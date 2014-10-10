{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell    #-}

module Database.DSH.FKL.Lang where

import           Text.PrettyPrint.ANSI.Leijen
import           Text.Printf

import           Database.DSH.Impossible
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

-- | 'Expr' is the target language of the flattening transformation.
data Expr l = Table Type String [L.Column] L.TableHints
            | PApp1 Type Prim1 l (Expr l)
            | PApp2 Type Prim2 l (Expr l) (Expr l)
            | PApp3 Type Prim3 l (Expr l) (Expr l) (Expr l)
            | If Type (Expr l) (Expr l) (Expr l)
            | BinOp Type L.ScalarBinOp l (Expr l) (Expr l)
            | UnOp Type L.ScalarUnOp l (Expr l)
            | Const Type L.Val
            | QConcat Nat  Type (Expr l)
            | UnConcat Nat Type (Expr l) (Expr l)
            | Let Type L.Ident (Expr l) (Expr l)
            | Var Type L.Ident
            | MkTuple Type l [Expr l]

type LExpr = Expr LiftedN
type FExpr = Expr Lifted

deriving instance Show (Expr LiftedN)
deriving instance Show (Expr Lifted)

-- | QuickConcat does not unsegment the vector. That is:
-- the descriptor might not be normalized and segment
-- descriptors other than 1 might occur. This is propably
-- ok when we know that a concated vector will be
-- unconcated again. We know this statically when
-- introducing concat/unconcat for higher-lifted
-- primitives.

data Prim1 = Length
           | Concat
           | TupElem TupleIndex
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
    deriving (Show, Eq)

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
           | Dist
           deriving (Show, Eq)

data Prim3 = Combine
    deriving (Show, Eq)

instance Typed (Expr l) where
    typeOf (Var t _)           = t
    typeOf (Let t _ _ _)       = t
    typeOf (Table t _ _ _)     = t
    typeOf (PApp1 t _ _ _)     = t
    typeOf (PApp2 t _ _ _ _)   = t
    typeOf (PApp3 t _ _ _ _ _) = t
    typeOf (If t _ _ _)        = t
    typeOf (BinOp t _ _ _ _)   = t
    typeOf (UnOp t _ _ _)      = t
    typeOf (Const t _)         = t
    typeOf (QConcat _ t _)     = t
    typeOf (UnConcat _ t _ _)  = t
    typeOf (MkTuple t _ _)     = t

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

instance Pretty Lifted where
    pretty Lifted    = text "ᴸ"
    pretty NotLifted = empty

instance Pretty LiftedN where
    pretty (LiftedN Zero) = empty
    pretty (LiftedN n)    = superscript (intFromNat n)

instance Pretty Prim1 where
    pretty Length       = text "length"
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
    pretty TupElem{}   = $impossible

instance Pretty Prim2 where
    pretty Group           = text "group"
    pretty Sort            = text "sort"
    pretty Dist            = text "dist"
    pretty Restrict        = text "restrict"
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

instance Pretty l => Pretty (Expr l) where
    pretty (MkTuple _ l es) = (tupled $ map pretty es) <> pretty l

    pretty (Var _ n) = text n
    pretty (Let _ x e1 e) = 
        align $ text "let" <+> text x {- <> colon <> colon <> pretty (typeOf e1) -} <+> char '=' <+> pretty e1
                <$>
                text "in" <+> pretty e

    pretty (Table _ n _c _k) = text "table" <> parens (text n)

    pretty (PApp1 _ (TupElem n) l e1) = 
        parenthize e1 <> dot <> int (tupleIndex n) <> pretty l

    pretty (PApp1 _ f l e1) =
        pretty f <> pretty l <+> (parenthize e1)

    pretty (PApp2 _ f l e1 e2) =
        pretty f <> pretty l <+> (align $ (parenthize e1) </> (parenthize e2))

    pretty (PApp3 _ f l e1 e2 e3) =
        pretty f <> pretty l
        <+> (align $ (parenthize e1) 
                     </> (parenthize e2) 
                     </> (parenthize e3))
    pretty (If _ e1 e2 e3) =
        let e1' = pretty e1
            e2' = pretty e2
            e3' = pretty e3
        in text "if" <+> e1'
           </> (nest 2 $ text "then" <+> e2')
           </> (nest 2 $ text "else" <+> e3')

    pretty (BinOp _ o l e1 e2) =
        align $ parenthize e1 </> pretty o <> pretty l </> parenthize e2

    pretty (UnOp _ o l e) =
        pretty o <> pretty l <> parens (pretty e)

    pretty (Const _ v) = pretty v

    pretty (QConcat n _ e) = 
        text "qconcat" 
        <> (angles $ int $ intFromNat n)
        <+> (parenthize e)

    pretty (UnConcat n _ e1 e2) = 
        text "unconcat" 
        <> (angles $ int $ intFromNat n) 
        <+> (align $ (parenthize e1) 
                     </> (parenthize e2))

parenthize :: Pretty l => Expr l -> Doc
parenthize e =
    case e of
        Const{}                 -> pretty e
        Table{}                 -> pretty e
        Var{}                   -> pretty e
        PApp1 _ (TupElem _) _ _ -> pretty e
        _                       -> parens $ pretty e
