module Language.ParallelLang.FKL.ProcessFKL where
    
import Language.ParallelLang.FKL.Data.FKL

isSimpleExpr :: Expr -> Bool
isSimpleExpr (Const _ _) = True
isSimpleExpr (Nil _) = True
isSimpleExpr (Var _ _ _) = True
isSimpleExpr _ = False

substitute :: String -> Expr -> Expr -> Expr
substitute n r e = substitute' e
 where
  substitute' :: Expr -> Expr
  substitute' (App t e1 es) = App t (substitute' e1) $ map substitute' es
  substitute' (Nil t) = Nil t
  substitute' v@(Fn t f i args e1) = case elem n (f:args) of
                                        True -> v
                                        False -> Fn t f i args $ substitute' e1
  substitute' (Let t x e1 e2) = case n == x of
                                    True -> Let t x (substitute' e1) e2
                                    False -> Let t x (substitute' e1) $ substitute' e2
  substitute' (If t e1 e2 e3) = If t (substitute' e1) (substitute' e2) $ substitute' e3
  substitute' (BinOp t o e1 e2) = BinOp t o (substitute' e1) $ substitute' e2
  substitute' v@(Var _ x _) = case n == x of
                            True -> r
                            False -> v
  substitute' v@(Const _ _) = v
  substitute' (Proj t l e1 i) = Proj t l (substitute' e1) i