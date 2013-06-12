%if False
\begin{code}

{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving    #-}

module Database.DSH.Flattening.NKL.Data.NKL 
  ( Expr(..)
  , Typed(..)
  , freeVars
  , Prim1Op(..)
  , Prim2Op(..)
  , Prim1(..)
  , Prim2(..)
  , Column
  , Key
  ) where

import           Text.PrettyPrint.HughesPJ

import           Database.DSH.Flattening.Common.Data.Op
import           Database.DSH.Flattening.Common.Data.Prim
import           Database.DSH.Flattening.Common.Data.Expr
import           Database.DSH.Flattening.Common.Data.Val(Val())
import           Database.DSH.Flattening.Common.Data.Type(Type, Typed, typeOf)
  
import qualified Data.Set as S

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
           |  AppE1 Type (Prim1 Type) Expr             -- \textrm{Application of a primitive to a single argument}
           |  AppE2 Type (Prim2 Type) Expr Expr        -- \textrm{Application of a primitive to two arguments}
           |  BinOp Type Oper Expr Expr         -- \textrm{Application of a binary opertor $\oplus$ to two arguments}
           |  Lam Type Ident Expr              -- \textrm{Lambda abstraction}
           |  If Type Expr Expr Expr            -- \textrm{Conditional}
           |  Const Type Val                    -- \textrm{Constant value}
           |  Var Type Ident                   -- \textrm{Variable}
\end{code}
}
%}
\NKLGrammar

%if False
\begin{code}
instance Show Expr where
  show e = render $ pp e

instance Typed Expr where
  typeOf (Table t _ _ _) = t
  typeOf (App t _ _)     = t
  typeOf (AppE1 t _ _)   = t
  typeOf (AppE2 t _ _ _) = t
  typeOf (Lam t _ _)     = t
  typeOf (If t _ _ _)    = t
  typeOf (BinOp t _ _ _) = t
  typeOf (Const t _)     = t
  typeOf (Var t _)       = t

pp :: Expr -> Doc
pp (Table _ n _ _)    = text "table" <+> text n
pp (App _ e1 e2)      = (parens $ pp e1) <+> (parens $ pp e2)
pp (AppE1 _ p1 e)     = (text $ show p1) <+> (parens $ pp e)
pp (AppE2 _ p1 e1 e2) = (text $ show p1) <+> (parens $ pp e1) <+> (parens $ pp e2)
pp (BinOp _ o e1 e2)  = (parens $ pp e1) <+> (text $ show o) <+> (parens $ pp e2)
pp (Lam _ v e)        = char '\\' <> text v <+> text "->" <+> pp e
pp (If _ c t e)       = text "if" <+> pp c <+> text "then" <+> (parens $ pp t) <+> text "else" <+> (parens $ pp e)
pp (Const _ v)        = text $ show v
pp (Var _ s)          = text s

deriving instance Eq Expr
deriving instance Ord Expr
\end{code}
%endif

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
