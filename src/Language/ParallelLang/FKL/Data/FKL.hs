{-# LANGUAGE GADTs, FlexibleInstances #-}
module Language.ParallelLang.FKL.Data.FKL where

import Language.ParallelLang.Common.Data.Op
import Language.ParallelLang.Common.Data.Val
import Language.ParallelLang.Common.Data.Type(Type, Typed, typeOf)
  
-- | Data type expr represents flat kernel language.
data Expr t where
    App   :: t -> Expr t -> [Expr t] -> Expr t-- | Apply multiple arguments to an expression
    Fn    :: t -> String -> Int -> [String] -> Expr t -> Expr t -- | A function has a name (and lifted level), some arguments and a body
    Let   :: t -> String -> Expr t -> Expr t -> Expr t -- | Let a variable have value expr1 in expr2
    If    :: t -> Expr t -> Expr t -> Expr t -> Expr t -- | If expr1 then expr2 else expr3
    BinOp :: t -> Op -> Expr t -> Expr t -> Expr t -- | Apply Op to expr1 and expr2 (apply for primitive infix operators)
    Const :: t -> Val -> Expr t -- | Constant value
    Var   :: t -> String -> Int -> Expr t -- | Variable lifted to level i
    Nil   :: t -> Expr t -- | []
    Proj  :: t -> Int -> Expr t -> Int -> Expr t
    deriving Eq
    
instance Typed (Expr Type) where
    typeOf (App t _ _) = t
    typeOf (Fn t _ _ _ _) = t
    typeOf (Let t _ _ _) = t
    typeOf (If t _ _ _) = t
    typeOf (BinOp t _ _ _) = t
    typeOf (Const t _) = t
    typeOf (Var t _ _) = t
    typeOf (Nil t) = t
    typeOf (Proj t _ _ _) = t
    
isTupleConstr :: Expr Type -> Bool
isTupleConstr (Var _ ('(':xs) _) = (==) ")" $ dropWhile (\x -> x == ',') xs 
isTupleConstr _ = False