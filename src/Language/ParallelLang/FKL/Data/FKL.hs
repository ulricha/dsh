{-# LANGUAGE GADTs #-}
module Language.ParallelLang.FKL.Data.FKL where

import Language.ParallelLang.Common.Data.Op
import Language.ParallelLang.Common.Data.Val
import Language.ParallelLang.Common.Data.Type(Type, Typed, typeOf)
  
-- | Data type expr represents flat kernel language.
data Expr where
    App   :: Type -> Expr -> [Expr] -> Expr -- | Apply multiple arguments to an expression
    Fn    :: Type -> String -> Int -> [String] -> Expr -> Expr -- | A function has a name (and lifted level), some arguments and a body
    Let   :: Type -> String -> Expr -> Expr -> Expr -- | Let a variable have value expr1 in expr2
    If    :: Type -> Expr -> Expr -> Expr -> Expr -- | If expr1 then expr2 else expr3
    BinOp :: Type -> Op -> Expr -> Expr -> Expr -- | Apply Op to expr1 and expr2 (apply for primitive infix operators)
    Const :: Type -> Val -> Expr -- | Constant value
    Var   :: Type -> String -> Int -> Expr  -- | Variable lifted to level i
    Nil   :: Type -> Expr -- | []
    Proj  :: Type -> Int -> Expr -> Int -> Expr
    deriving Eq
    
instance Typed Expr where
    typeOf (App t _ _) = t
    typeOf (Fn t _ _ _ _) = t
    typeOf (Let t _ _ _) = t
    typeOf (If t _ _ _) = t
    typeOf (BinOp t _ _ _) = t
    typeOf (Const t _) = t
    typeOf (Var t _ _) = t
    typeOf (Nil t) = t
    typeOf (Proj t _ _ _) = t
    
isTupleConstr :: Expr -> Bool
isTupleConstr (Var _ ('(':xs) _) = (==) ")" $ dropWhile (\x -> x == ',') xs 
isTupleConstr _ = False