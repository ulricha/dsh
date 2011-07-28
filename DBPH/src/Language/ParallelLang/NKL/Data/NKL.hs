{-# LANGUAGE GADTs, FlexibleInstances, MultiParamTypeClasses  #-}
module Language.ParallelLang.NKL.Data.NKL (Expr, Ex(..), Typed(..), freeVars) where

import Language.ParallelLang.Common.Data.Op
import Language.ParallelLang.Common.Data.Val
import Language.ParallelLang.Common.Data.Type(Type, Typed, typeOf)

import qualified Data.Set as S

type Column t = (String, t)

type Key = [String]

type Expr = Ex Type
-- | Data type expr represents nested kernel language.
data Ex t where
    Table :: t -> String -> [Column t] -> [Key] -> Ex t
    App   :: t -> Expr -> Ex t -> Ex t -- | Apply multiple arguments to an expression
    Tuple :: t -> [Ex t] -> Ex t
    Lam   :: t -> String -> Ex t -> Ex t -- | A function has a name, some arguments and a body
    Let   :: t -> String -> Ex t -> Ex t -> Ex t -- | Let a variable have value expr1 in expr2
    If    :: t -> Ex t -> Ex t -> Ex t -> Ex t -- | If expr1 then expr2 else expr3
    BinOp :: t -> Op -> Ex t -> Ex t -> Ex t -- | Apply Op to expr1 and expr2 (apply for primitive infix operators)
    Const :: t -> Val -> Ex t -- | Constant value
    Var   :: t -> String -> Ex t  -- | Variable
    Iter  :: t -> String -> Ex t -> Ex t -> Ex t -- | [expr2 | var <- expr1]
    Nil   :: t -> Ex t -- | []
    Proj  :: t -> Int -> Ex t -> Int -> Ex t  
      deriving (Show, Eq, Ord)

instance Typed Ex Type where
    typeOf (Table t _ _ _) = t
    typeOf (App t _ _) = t
    typeOf (Lam t _ _) = t
    typeOf (Let t _ _ _) = t
    typeOf (If t _ _ _) = t
    typeOf (BinOp t _ _ _) = t
    typeOf (Const t _) = t
    typeOf (Var t _) = t
    typeOf (Iter t _ _ _) = t
    typeOf (Tuple t _) = t
    typeOf (Nil t) = t
    typeOf (Proj t _ _ _) = t

freeVars :: [String] -> Expr -> S.Set (String, Expr)
freeVars _ (Table _ _ _ _) = S.empty
freeVars t (App _ e1 es) = freeVars t e1 `S.union` (freeVars t es)
freeVars t (Lam _ x e) = freeVars (x:t) e 
freeVars t (Let _ x e1 e2) = freeVars t e1 `S.union` freeVars (x:t) e2
freeVars t (If _ e1 e2 e3) = S.unions [freeVars t e1, freeVars t e2, freeVars t e3]
freeVars t (BinOp _ _ e1 e2) = freeVars t e1 `S.union` freeVars t e2
freeVars _ (Const _ _) = S.empty
freeVars t v@(Var _ x) = if x `elem` t then S.empty else S.singleton (x, v)
freeVars t (Iter _ x e1 e2) = freeVars t e1 `S.union` freeVars (x:t) e2
freeVars _ (Nil _) = S.empty
freeVars t (Proj _ _ e _) = freeVars t e
freeVars t (Tuple _ es) = S.unions $ map (freeVars t) es
    