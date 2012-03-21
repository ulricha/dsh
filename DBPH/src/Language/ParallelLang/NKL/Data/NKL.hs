{-# LANGUAGE GADTs, FlexibleInstances, MultiParamTypeClasses  #-}
module Language.ParallelLang.NKL.Data.NKL (Expr(..), Typed(..), freeVars, Prim1(..), Prim2(..)) where

import Language.ParallelLang.Common.Data.Op
import Language.ParallelLang.Common.Data.Val(Val())
import Language.ParallelLang.Common.Data.Type(Type, Typed, typeOf)

import qualified Data.Set as S

type Column = (String, Type)

type Key = [String]

-- | Data type expr represents nested kernel language.
data Expr where
    Table :: Type -> String -> [Column] -> [Key] -> Expr
    App   :: Type -> Expr -> Expr -> Expr -- | Apply multiple arguments to an expression
    AppE1 :: Type -> Prim1 -> Expr -> Expr
    AppE2 :: Type -> Prim2 -> Expr -> Expr -> Expr 
    BinOp :: Type -> Op -> Expr -> Expr -> Expr -- | Apply Op to expr1 and expr2 (apply for primitive infix operators)
    -- Pair  :: Type -> Expr -> Expr -> Expr
    Lam   :: Type -> String -> Expr -> Expr -- | A function has a name, some arguments and a body
    Let   :: Type -> String -> Expr -> Expr -> Expr -- | Let a variable have value expr1 in expr2
    If    :: Type -> Expr -> Expr -> Expr -> Expr -- | If expr1 then expr2 else expr3
    Const :: Type -> Val -> Expr -- | Constant value
    Var   :: Type -> String -> Expr  -- | Variable
    -- FIXME Delete next line
    -- Iter  :: Type -> String -> Expr -> Expr -> Expr -- | [expr2 | var <- expr1]
    -- Nil   :: Type -> Expr -- | []
    -- Fst   :: Type -> Expr -> Expr
    -- Snd   :: Type -> Expr -> Expr
      deriving (Show, Eq, Ord)

data Prim1 = Length Type
           | Not Type
           | Concat Type
           | Sum Type
           | The Type
           | Fst Type
           | Snd Type
    deriving (Show, Eq, Ord)

data Prim2 = Map Type
           | GroupWith Type
           | SortWith Type
           | Pair Type
    deriving (Show, Eq, Ord)

instance Typed Expr where
    typeOf (Table t _ _ _) = t
    typeOf (App t _ _) = t
    typeOf (AppE1 t _ _) = t
    typeOf (AppE2 t _ _ _) = t
    typeOf (Lam t _ _) = t
    typeOf (Let t _ _ _) = t
    typeOf (If t _ _ _) = t
    typeOf (BinOp t _ _ _) = t
    typeOf (Const t _) = t
    typeOf (Var t _) = t
    -- typeOf (Iter t _ _ _) = t
    -- typeOf (Pair t _ _) = t
    -- typeOf (Nil t) = t
    -- typeOf (Fst t _) = t
    -- typeOf (Snd t _) = t

freeVars :: [String] -> Expr -> S.Set (String, Expr)
freeVars _ (Table _ _ _ _) = S.empty
freeVars t (App _ e1 es) = freeVars t e1 `S.union` (freeVars t es)
freeVars t (AppE1 _ _ e1) = freeVars t e1
freeVars t (AppE2 _ _ e1 e2) = freeVars t e1 `S.union` freeVars t e2
freeVars t (Lam _ x e) = freeVars (x:t) e 
freeVars t (Let _ x e1 e2) = freeVars t e1 `S.union` freeVars (x:t) e2
freeVars t (If _ e1 e2 e3) = S.unions [freeVars t e1, freeVars t e2, freeVars t e3]
freeVars t (BinOp _ _ e1 e2) = freeVars t e1 `S.union` freeVars t e2
freeVars _ (Const _ _) = S.empty
freeVars t v@(Var _ x) = if x `elem` t then S.empty else S.singleton (x, v)
-- freeVars t (Iter _ x e1 e2) = freeVars t e1 `S.union` freeVars (x:t) e2
-- freeVars _ (Nil _) = S.empty
-- freeVars t (Fst _ e) = freeVars t e
-- freeVars t (Snd _ e) = freeVars t e
-- freeVars t (Pair _ e1 e2) = freeVars t e1 `S.union` freeVars t e2
    
