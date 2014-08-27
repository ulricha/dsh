module Database.DSH.FKL.Pretty where

import           Data.List                    (intersperse)
import           Text.PrettyPrint.ANSI.Leijen
import           Text.Printf

import           Database.DSH.Common.Lang
import           Database.DSH.Common.Pretty
import           Database.DSH.FKL.Lang


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

