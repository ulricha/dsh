module Language.ParallelLang.FKL.Render.Render where
    
import Language.ParallelLang.FKL.Data.FKL
import Language.ParallelLang.Common.Data.Val

import Text.PrettyPrint hiding (render)
import Data.List (intersperse)

instance Show (Expr t) where
   show a = show $ render a
    
render :: Expr t -> Doc
render (Table _ n _c _k) = parens $ text "Table" <+> text n
render (Labeled _ e) = render e
render (PApp1 _ f e1) = text (show f) <+> (parens $ render e1)
render (PApp2 _ f e1 e2) = text (show f) <+> (parens $ render e1) <+> (parens $ render e2)
render (PApp3 _ f e1 e2 e3) = text (show f) <+> (parens $ render e1) <+> (parens $ render e2) <+> (parens $ render e3)
render (Let _ x e1 e2) = let e1' = render e1
                             e2' = render e2
                          in text "let" <+> text x <+> text "=" <+> e1'
                               $+$ (nest 2 $ text "in" <+> e2')
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
render (Clo _ l vs x f fl) = text "<<" <+> text (l ++ ", ") <+> text (show vs) <> text ", \\" <+> text x  <+> text " -> " <+> render f <> text ", \\" <+> text x <+> text " -> "<+> render fl <> text ">>"
render (AClo _ vs x f fl) = text "<<" <+> text (show vs) <> text ", \\" <+> text x <+> text " -> " <+> render f <> text ", \\" <+> text x <+> text " -> " <+> render fl <> text ">>+"
render (CloApp _ f a) = render f <+> text ":$" <+> render a
render (CloLApp _ f a) = render f <+> text ":$l" <+> render a
render (Nil _) = text "[]" 
render (Proj _ 0 e i) = parens (render e) <> text "@" <> text (show i) 
render (Proj _ l e i) = parens (render e) <> text "@^" <> text (show l) <+> text (show i) 
-- render (Tuple _ es) = parens (hsep $ intersperse comma $ map render es) 
render (Pair _ e1 e2) = parens (render e1 <> comma <+> render e2)

renderC :: Val -> Doc
renderC (Int i) = int i
renderC (String s) = text $ show s
renderC (Double d) = double d
renderC (Bool b) = text $ show b
renderC (Unit) = text $ "()"
renderC (List es) = text "[" <> hsep (intersperse comma $ map renderC es) <> text "]"