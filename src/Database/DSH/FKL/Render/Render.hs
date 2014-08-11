module Database.DSH.FKL.Render.Render where

import           Database.DSH.Common.Lang
import           Database.DSH.FKL.Data.FKL

import           Data.List                 (intersperse)
import           Text.PrettyPrint.ANSI.Leijen

instance Pretty a => Pretty (Lifted a) where
    pretty (Lifted a)    = pretty a <> text "^L"
    pretty (NotLifted a) = pretty a

instance Pretty Expr where
    pretty (Table _ n _c _k) = parens $ text "Table" <+> text n

    pretty (PApp1 _ f e1) = 
        text (show f) 
        <+> (parens $ pretty e1)
    
    pretty (PApp2 _ f e1 e2) = 
        text (show f) <+> (align $ (parens $ pretty e1) <$> (parens $ pretty e2))
    
    pretty (PApp3 _ f e1 e2 e3) = 
        text (show f) <+> (align $ (parens $ pretty e1) <$> (parens $ pretty e2) <$> (parens $ pretty e3))
    
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
    
    pretty (Var _ x) = 
        text x
    
    pretty (Clo _ l vs x f fl) = 
        encloseSep lcloangle rcloangle comma [text l <+> text (show vs), lambda x f, lambda x fl]
      where
        lcloangle = text "<<"
        rcloangle = text ">>"
    
    pretty (AClo _ l vs x f fl) = 
        encloseSep lcloangle racloangle comma [text l <+> text (show vs), lambda x f, lambda x fl]
      where
        lcloangle = text "<<"
        racloangle = text ">>+"
    
    pretty (CloApp _ f a) = parens $ align $ pretty f </> text ":$" </> (parens $ pretty a)
    
    pretty (CloLApp _ f a) = parens $ align $ pretty f </> text ":$l" </> (parens $ pretty a)

lambda :: Ident -> Expr -> Doc
lambda x e = char '\\' <> text x <+> text "->" <+> pretty e

cloAngles :: Doc -> Doc
cloAngles = angles . angles

acloAngles :: Doc -> Doc
acloAngles d = (angles $ angles d) <> char '+'
    
renderC :: Val -> Doc
renderC (IntV i)      = int i
renderC (StringV s)   = text $ show s
renderC (DoubleV d)   = double d
renderC (BoolV b)     = text $ show b
renderC (UnitV)       = text $ "()"
renderC (ListV es)    = text "[" <> hsep (intersperse comma $ map renderC es) <> text "]"
renderC (PairV e1 e2) = text "(" <> renderC e1 <> comma <+> renderC e2 <> text ")"
