{-# LANGUAGE GADTs, FlexibleInstances, MultiParamTypeClasses, ScopedTypeVariables, ExistentialQuantification #-}
module Language.ParallelLang.FKL.Data.FKL where

import Language.ParallelLang.Common.Data.TypeRestrictions 
import Language.ParallelLang.Common.Data.Op
import Language.ParallelLang.Common.Data.Val
-- import Language.ParallelLang.Common.Data.Type(Type, Typed, typeOf)

data Expr t where
    Labeled :: QT t => String -> Expr t -> Expr t
    App     :: forall a b. (QT a, QT b) => Expr (a -> b) -> Expr a -> Expr b 
    Fn      :: (QT a, QT b) => String -> Expr b -> Expr (a -> b)
    Let     :: forall a b. (QT a, QT b) => String -> Expr a -> Expr b -> Expr b
    If      :: Expr Bool -> Expr a -> Expr a -> Expr a
    BinOp   :: forall a b c. (QT a, QT b, QT c) => Op (a -> b -> c) -> Expr a -> Expr b -> Expr c
    Const   :: RT a => Val a -> Expr a
    Var     :: QT a => String -> Expr a
    Nil     :: QT a => Expr a
    Proj    :: forall a b. (QT a, QT b) => Expr a -> Int -> Expr b
    
{-
-- | Data type expr represents flat kernel language.
data Expr t where
    Labeled :: String -> Expr t -> Expr t -- | Constructor for debugging purposes
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

instance Typed Expr t where
    typeOf (App t _ _) = t
    typeOf (Fn t _ _ _ _) = t
    typeOf (Let t _ _ _) = t
    typeOf (If t _ _ _) = t
    typeOf (BinOp t _ _ _) = t
    typeOf (Const t _) = t
    typeOf (Var t _ _) = t
    typeOf (Nil t) = t
    typeOf (Proj t _ _ _) = t
    typeOf (Labeled _ e) = typeOf e
    
isTupleConstr :: Expr Type -> Bool
isTupleConstr (Var _ ('(':xs) _) = (==) ")" $ dropWhile (\x -> x == ',') xs 
isTupleConstr _ = False
-}