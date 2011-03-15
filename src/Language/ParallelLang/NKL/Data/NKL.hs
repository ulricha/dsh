{-# LANGUAGE GADTs, FlexibleInstances, MultiParamTypeClasses  #-}
module Language.ParallelLang.NKL.Data.NKL where

import Language.ParallelLang.Common.Data.Op
import Language.ParallelLang.Common.Data.Val
import Language.ParallelLang.Common.Data.Type(Type, Typed, typeOf)

type Expr = Ex Type
-- | Data type expr represents nested kernel language.
data Ex t where
    App   :: t -> Expr -> [Ex t] -> Ex t -- | Apply multiple arguments to an expression
    Fn    :: t -> String -> Int -> [String] -> Ex t -> Ex t -- | A function has a name, some arguments and a body
    Let   :: t -> String -> Ex t -> Ex t -> Ex t -- | Let a variable have value expr1 in expr2
    If    :: t -> Expr -> Ex t -> Ex t -> Ex t -- | If expr1 then expr2 else expr3
    BinOp :: t -> Op -> Ex t -> Ex t -> Ex t -- | Apply Op to expr1 and expr2 (apply for primitive infix operators)
    Const :: t -> Val -> Ex t -- | Constant value
    Var   :: t -> String -> Int -> Ex t  -- | Variable
    Iter  :: t -> String -> Ex t -> Ex t -> Ex t -- | [expr2 | var <- expr1]
    IterG :: t -> String -> Ex t -> Ex t -> Ex t -> Ex t -- | [expr3 | var <- expr1, expr2]
    Nil   :: t -> Ex t -- | []
    Proj  :: t -> Int -> Ex t -> Int -> Ex t    

instance Typed Ex t where
    typeOf (App t _ _) = t
    typeOf (Fn t _ _ _ _) = t
    typeOf (Let t _ _ _) = t
    typeOf (If t _ _ _) = t
    typeOf (BinOp t _ _ _) = t
    typeOf (Const t _) = t
    typeOf (Var t _ _) = t
    typeOf (Iter t _ _ _) = t
    typeOf (IterG t _ _ _ _) = t
    typeOf (Nil t) = t
    typeOf (Proj t _ _ _) = t