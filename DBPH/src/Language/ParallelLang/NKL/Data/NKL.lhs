%if False
\begin{code}
{-# LANGUAGE GADTs, FlexibleInstances, MultiParamTypeClasses, StandaloneDeriving  #-}
module Language.ParallelLang.NKL.Data.NKL (Expr(..), Typed(..), freeVars, Prim1(..), Prim2(..), Column, Key) where

import Language.ParallelLang.Common.Data.Op
import Language.ParallelLang.Common.Data.Val(Val())
import Language.ParallelLang.Common.Data.Type(Type, Typed, typeOf)

import qualified Data.Set as S

type Column = (String, Type)

type Key = [String]
\end{code}
%endif
%{
%include syntaxdef.fmt
%include nkl.fmt
The following syntax diagram describes our input language, the Nested Kernel Language. 
% The code below defines the NKL grammar
\newcommand{\NKLGrammar}{
\begin{code}
data Expr  =  Table Type String [Column] [Key]  -- \textrm{Reference database table $n$}
           |  App Type Expr Expr                -- \textrm{Application of two expressions}
           |  AppE1 Type Prim1 Expr             -- \textrm{Application of a primitive to a single argument}
           |  AppE2 Type Prim2 Expr Expr        -- \textrm{Application of a primitive to two arguments}
           |  BinOp Type Oper Expr Expr         -- \textrm{Application of a binary opertor $\oplus$ to two arguments}
           |  Lam Type String Expr              -- \textrm{Lambda abstraction}
           |  If Type Expr Expr Expr            -- \textrm{Conditional}
           |  Const Type Val                    -- \textrm{Constant value}
           |  Var Type String                   -- \textrm{Variable}
\end{code}
}
%}
\NKLGrammar

%if False
\begin{code}
deriving instance Show Expr
deriving instance Eq Expr
deriving instance Ord Expr
\end{code}
%endif

The primitive operations supported by the NKL are the following:

Unary primitive operations:
%{
%include syntaxdef.fmt
%include NKLPrims.fmt
\begin{code}
data Prim1  =  Length Type  |  Not Type  |  Concat Type
            |  Sum Type | The Type | Fst Type | Snd Type
            |  Head Type | Minimum Type | Maximum Type 
            |  IntegerToDouble Type | Tail Type
            |  Reverse Type | And Type | Or Type
            |  Init Type | Last Type | Nub Type
\end{code}

%if False
\begin{code}
deriving instance Show Prim1
deriving instance Eq Prim1
deriving instance Ord Prim1    
\end{code}
%endif

Binary primitive operations:

\begin{code}
data Prim2  =  Map Type | GroupWith Type
            |  SortWith Type | Pair Type
            |  Filter Type | Append Type
            |  Index Type | Take Type
            |  Drop Type | Zip Type
\end{code}
%}
%if False
\begin{code}
deriving instance Show Prim2
deriving instance Eq Prim2
deriving instance Ord Prim2
\end{code}
\begin{code}
instance Typed Expr where
    typeOf (Table t _ _ _) = t
    typeOf (App t _ _) = t
    typeOf (AppE1 t _ _) = t
    typeOf (AppE2 t _ _ _) = t
    typeOf (Lam t _ _) = t
    typeOf (If t _ _ _) = t
    typeOf (BinOp t _ _ _) = t
    typeOf (Const t _) = t
    typeOf (Var t _) = t
\end{code}
%endif

We define a function |fvs| to compute the set of free variable in an NKL-expression:
%{
%include nkl.fmt
%format (freeVars (x)) = " fvs (" x ") "
%format `S.union` = " \cup "
%format S.empty = " \emptyset "
%format (S.singleton (x)) = " \{ x \} "

\begin{code}
freeVars :: Expr -> S.Set String
freeVars (Table _ _ _ _) = S.empty
freeVars (App _ e1 e2) = freeVars e1 `S.union` freeVars e2
freeVars (AppE1 _ _ e1) = freeVars e1
freeVars (AppE2 _ _ e1 e2) = freeVars e1 `S.union` freeVars e2
freeVars (Lam _ x e) = (freeVars e) S.\\ S.singleton x
freeVars (If _ e1 e2 e3) = freeVars e1 `S.union` freeVars e2 `S.union` freeVars e3
freeVars (BinOp _ _ e1 e2) = freeVars e1 `S.union` freeVars e2
freeVars (Const _ _) = S.empty
freeVars (Var _ x) = S.singleton x
\end{code}
%}
