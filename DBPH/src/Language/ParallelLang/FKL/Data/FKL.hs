{-# LANGUAGE GADTs, FlexibleInstances, MultiParamTypeClasses #-}
module Language.ParallelLang.FKL.Data.FKL where

import Language.ParallelLang.Common.Data.Op
import Language.ParallelLang.Common.Data.Val
import Language.ParallelLang.Common.Data.Type(Type, Typed, typeOf)

-- | Data type expr represents flat kernel language.
data Expr t where
    Labeled :: String -> Expr t -> Expr t -- | Constructor for debugging purposes
    App     :: t -> Expr t -> [Expr t] -> Expr t-- | Apply multiple arguments to an expression
    CloApp  :: t -> Expr t -> [Expr t] -> Expr t
    CloLApp :: t -> Expr t -> [Expr t] -> Expr t
    Lam     :: t -> String -> Expr t -> Expr t -- | A function has a name (and lifted level), some arguments and a body
    Let     :: t -> String -> Expr t -> Expr t -> Expr t -- | Let a variable have value expr1 in expr2
    If      :: t -> Expr t -> Expr t -> Expr t -> Expr t -- | If expr1 then expr2 else expr3
    BinOp   :: t -> Op -> Expr t -> Expr t -> Expr t -- | Apply Op to expr1 and expr2 (apply for primitive infix operators)
    Const   :: t -> Val -> Expr t -- | Constant value
    Var     :: t -> String -> Expr t -- | Variable lifted to level i
    Nil     :: t -> Expr t -- | []
    Proj    :: t -> Int -> Expr t -> Int -> Expr t
    Clo     :: t -> [String] -> Expr t -> Expr t -> Expr t
    AClo    :: t -> [String] -> Expr t -> Expr t -> Expr t
    deriving Eq



instance Typed Expr t where
    typeOf (App t _ _) = t
    typeOf (Lam t _ _) = t
    typeOf (Let t _ _ _) = t
    typeOf (If t _ _ _) = t
    typeOf (BinOp t _ _ _) = t
    typeOf (Const t _) = t
    typeOf (Var t _) = t
    typeOf (Nil t) = t
    typeOf (Proj t _ _ _) = t
    typeOf (Labeled _ e) = typeOf e
--    typeOf ()
    
isTupleConstr :: Expr Type -> Bool
isTupleConstr (Var _ ('(':xs)) = (==) ")" $ dropWhile (\x -> x == ',') xs 
isTupleConstr _ = False