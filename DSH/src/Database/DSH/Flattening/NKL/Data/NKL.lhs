%if False
\begin{code}
{-# LANGUAGE GADTs, FlexibleInstances, MultiParamTypeClasses, StandaloneDeriving  #-}
module Database.DSH.Flattening.NKL.Data.NKL (Expr(..), Typed(..), freeVars, Prim1(..), Prim2(..), Column, Key) where

import           Text.PrettyPrint.HughesPJ

import           Database.DSH.Flattening.Common.Data.Op
import           Database.DSH.Flattening.Common.Data.Val(Val())
import           Database.DSH.Flattening.Common.Data.Type(Type, Typed, typeOf)
  
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
           |  AppE1 Type (Prim1 Type) Expr             -- \textrm{Application of a primitive to a single argument}
           |  AppE2 Type (Prim2 Type) Expr Expr        -- \textrm{Application of a primitive to two arguments}
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
instance Show Expr where
  show e = render $ pp e
  
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

The primitive operations supported by the NKL are the following:

Unary primitive operations:
%{
%include syntaxdef.fmt
%include NKLPrims.fmt
\begin{code}
data Prim1 t =  Length t  |  Not t  |  Concat t
             |  Sum t | Avg t | The t | Fst t | Snd t
             |  Head t | Minimum t | Maximum t
             |  IntegerToDouble t | Tail t
             |  Reverse t | And t | Or t
             |  Init t | Last t | Nub t
             deriving (Eq, Ord)
\end{code}

%if False
\begin{code}

instance Show (Prim1 t) where
  show (Length _) = "length"
  show (Not _) = "not"
  show (Concat _) = "concat"
  show (Sum _) = "sum"
  show (Avg _) = "avg"
  show (The _) = "the"
  show (Fst _) = "fst"
  show (Snd _) = "snd"
  show (Head _) = "head"
  show (Minimum _) = "minimum"
  show (Maximum _) = "maximum"
  show (IntegerToDouble _) = "integerToDouble"
  show (Tail _) = "tail"
  show (Reverse _) = "reverse"
  show (And _) = "and"
  show (Or _) = "or"
  show (Init _) = "init"
  show (Last _) = "last"
  show (Nub _) = "nub"

\end{code}
%endif

Binary primitive operations:

\begin{code}
data Prim2  t = Map t | GroupWithKey t
              | SortWith t | Pair t
              | Filter t | Append t
              | Index t | Take t
              | Drop t | Zip t
              | TakeWhile t
              | DropWhile t
              | CartProduct t
              deriving (Eq, Ord)
\end{code}
%}
%if False
\begin{code}
instance Show (Prim2 t) where
  show (Map _) = "map"
  show (GroupWithKey _) = "groupWithKey"
  show (SortWith _) = "sortWith"
  show (Pair _) = "pair"
  show (Filter _) = "filter"
  show (Append _) = "append"
  show (Index _) = "index"
  show (Take _) = "take"
  show (Drop _) = "drop"
  show (Zip _) = "zip"
  show (TakeWhile _) = "takeWhile"
  show (DropWhile _) = "dropWhile"
  show (CartProduct _) = "cartProduct"

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
