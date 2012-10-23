module Database.DSH.Flattening.NKL.Opt where

import Database.DSH.Flattening.NKL.Data.NKL
import Database.DSH.Flattening.Common.Data.Val
import Database.DSH.Flattening.Common.Data.Op

-- Perform simple optimizations on the NKL
opt :: Expr -> Expr
opt e =
  case e of 
    tab@(Table _ _ _ _) -> tab
    App t e1 e2 -> App t (opt e1) (opt e2)
    {-
    Transform the concatMap pattern resulting from the desugaring of 
    predicates in monad comprehensions into a simple conditional.

       concat $ map (\_ -> [_body_]) (if _predicate_ ([()]) ([]))
    => if _predicate_ _body_ []
    -}
    AppE1 t 
          (Concat _) 
          (AppE2 _ 
                 (Map _)
                 (Lam _
                      _
                      body@(BinOp bodyType Cons _ (Const _ (List []))))
                 (If _ predicate (Const _ (List [Unit])) (Const _ (List [])))) ->
            If t predicate body (Const bodyType (List []))
    AppE1 t p1 e1 -> AppE1 t p1 (opt e1)
    AppE2 t p1 e1 e2 -> AppE2 t p1 (opt e1) (opt e2)
    BinOp t op e1 e2 -> BinOp t op (opt e1) (opt e2)
    Lam t v e1 -> Lam t v (opt e1)
    If t ce te ee -> If t (opt ce) (opt te) (opt ee)
    constant@(Const _ _) -> constant
    var@(Var _ _) -> var
