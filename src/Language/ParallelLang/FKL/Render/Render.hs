module Language.ParallelLang.FKL.Render.Render where
    
import Language.ParallelLang.FKL.Data.FKL
import Language.ParallelLang.Common.Data.Val
import Language.ParallelLang.Common.Data.Op

import Text.PrettyPrint hiding (render)
import Data.List (intersperse)

instance Show (Expr t) where
   show a = show $ render a
    
render :: Expr t -> Doc
render (Labeled _ e) = render e
render (App _ e1 e2) = let e2' = map render e2
                        in parens $ render e1 <+> hsep e2'
render (Lam _ arg e) = text "\\" <+> text arg <+> text "->"
                            $+$ render e
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
render (BinOp _ (Op o 0) e1 e2) = let e1' = render e1
                                      e2' = render e2
                                   in parens $ e1' <+> text o <+> e2'
render (BinOp _ (Op o i) e1 e2) = let e1' = render e1
                                      e2' = render e2
                                   in parens $ e1' <+> text o <> text "^" <> int i <+> e2'
render (Const _ (Int i)) = int i
render (Const _ (String s)) = text $ show s
render (Const _ (Double d)) = double d
render (Const _ (Bool b)) = text $ show b
render (Const _ (Unit)) = text $ "()"
render (Var _ x) = text x
render (Clo _ l vs x f fl) = text "<<" <+> text (l ++ ", ") <+> text (show vs) <> text ", \\" <+> text x  <+> text " -> " <+> render f <> text ", \\" <+> text x <+> text " -> "<+> render fl <> text ">>"
render (AClo _ vs x f fl) = text "<<" <+> text (show vs) <> text ", \\" <+> text x <+> text " -> " <+> render f <> text ", \\" <+> text x <+> text " -> " <+> render fl <> text ">>+"
render (CloApp _ f a) = render f <+> text ":$" <+> render a
render (CloLApp _ f a) = render f <+> text ":$l" <+> render a
-- render (Cons x xs) = text "(" <> render x <> text ":" <> render xs <> text ")"
render (Nil _) = text "[]" 
-- render (Tuple es) = text "(" <> hcat (intersperse (text ", ") $ map render es) <> text ")"
render (Proj _ 0 e i) = parens (render e) <> text "@" <> text (show i) 
render (Proj _ l e i) = parens (render e) <> text "@^" <> text (show l) <+> text (show i) 
render (Tuple _ es) = parens (hsep $ intersperse comma $ map render es) 
{-
renderLiftLevel :: Int -> String
rednerLiftLevel i = "⁰¹²³⁴⁵⁶⁷⁸⁹"
-}