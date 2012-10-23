module Language.ParallelLang.FKL.Render.Render where
    
import Language.ParallelLang.FKL.Data.FKL
import qualified Language.ParallelLang.Common.Data.Val as V

import Text.PrettyPrint hiding (render)
import Data.List (intersperse)

instance Show Expr where
   show a = show $ render a
    
render :: Expr -> Doc
render (Table _ n _c _k) = parens $ text "Table" <+> text n
render (PApp1 _ f e1) = text (show f) <+> (parens $ render e1)
render (PApp2 _ f e1 e2) = text (show f) <+> (parens $ render e1) <+> (parens $ render e2)
render (PApp3 _ f e1 e2 e3) = text (show f) <+> (parens $ render e1) <+> (parens $ render e2) <+> (parens $ render e3)
render (If _ e1 e2 e3) = let e1' = render e1
                             e2' = render e2
                             e3' = render e3
                          in text "if" <+> e1'
                              $+$ (nest 2 $ text "then" <+> e2')
                              $+$ (nest 2 $ text "else" <+> e3')
render (BinOp _ o e1 e2) = let e1' = render e1
                               e2' = render e2
                            in parens $ e1' <+> text (show o) <+> e2'
render (Const _ v) = renderC v
render (Var _ x) = text x
render (Clo _ l vs x f fl) = text "<<" <+> text (l ++ ", ") <+> text (show vs) <> text ", \\" <+> text x  <+> text " -> " <+> render f <> text ", \\" <+> text x <+> text " -> "<+> render fl  <> text ">>"
render (AClo _ l vs x f fl) = text "<<" <+> text l <+> text (show vs) <> text ", \\" <+> text x <+> text " -> " <+> render f <> text ", \\" <+> text x <+> text " -> " <+> render fl <> text ">>+"
render (CloApp _ f a) = parens $ render f <+> text ":$" <+> (parens $ render a)
render (CloLApp _ f a) = parens $ render f <+> text ":$l" <+> (parens $ render a)

renderC :: V.Val -> Doc
renderC (V.Int i) = int i
renderC (V.String s) = text $ show s
renderC (V.Double d) = double d
renderC (V.Bool b) = text $ show b
renderC (V.Unit) = text $ "()"
renderC (V.List es) = text "[" <> hsep (intersperse comma $ map renderC es) <> text "]"
renderC (V.Pair e1 e2) = text "(" <> renderC e1 <> comma <+> renderC e2 <> text ")"
