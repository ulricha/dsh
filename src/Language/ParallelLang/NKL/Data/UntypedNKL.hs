{-# LANGUAGE GADTs #-}
module Language.ParallelLang.NKL.Data.UntypedNKL where

import Language.ParallelLang.Common.Data.Op
import Language.ParallelLang.Common.Data.Val
import Language.ParallelLang.Common.Data.Type 

-- | Data type expr represents nested kernel language.
data Expr where
    App :: Expr -> [Expr] -> Expr -- | Apply multiple arguments to an expression
    Fn :: String -> Int -> [String] -> Expr -> Maybe Type -> Expr -- | A function has a name, some arguments and a body
    Let :: String -> Expr -> Expr -> Expr -- | Let a variable have value expr1 in expr2
    If :: Expr -> Expr -> Expr -> Expr -- | If expr1 then expr2 else expr3
    BinOp :: Op -> Expr -> Expr -> Expr -- | Apply Op to expr1 and expr2 (apply for primitive infix operators)
    Const :: Val -> Expr -- | Constant value
    Var :: String -> Int -> Expr  -- | Variable
    Iter :: String -> Expr -> Expr -> Expr -- | [expr2 | var <- expr1]
    IterG :: String -> Expr -> Expr -> Expr -> Expr -- | [expr3 | var <- expr1, expr2]
    Nil :: Expr -- | []
    Proj :: Int -> Expr -> Int -> Expr -- | Projection on tuples is a primitive operation, as it is lifted differently (with the database in mind)
    Typed :: Expr -> Type -> Expr