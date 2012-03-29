%if False
\begin{code}
{-# LANGUAGE TemplateHaskell, TupleSections #-}
module Language.ParallelLang.Translate.NKL2FKL (flatTransform) where

import qualified Language.ParallelLang.FKL.Data.FKL as F
import qualified Language.ParallelLang.NKL.Data.NKL as N
import Language.ParallelLang.Translate.TransM

import Language.ParallelLang.FKL.Primitives
import Language.ParallelLang.Common.Data.Type

import qualified Data.Set as S

import Control.Applicative

flatTransform :: N.Expr -> TransM F.Expr
flatTransform = transform 

prim1Transform :: N.Prim1 -> F.Expr
prim1Transform (N.Length t) = lengthVal t
prim1Transform (N.Not t) = notVal t
prim1Transform (N.Concat t) = concatVal t
prim1Transform (N.Sum t) = sumVal t
prim1Transform (N.The t) = theVal t
prim1Transform (N.Fst t) = fstVal t
prim1Transform (N.Snd t) = sndVal t

prim2Transform :: N.Prim2 -> F.Expr
prim2Transform (N.Map t) = mapVal t
prim2Transform (N.SortWith t) = sortWithVal t
prim2Transform (N.GroupWith t) = groupWithVal t
prim2Transform (N.Pair t) = pairVal t 
\end{code}
%endif

%format (transform (x)) = " \mathcal{T} \llbracket " x " \rrbracket "
%format (lift (n) (e)) = " \mathcal{L} \llbracket " e " \rrbracket " n
%format pure = " "
%format $ = " "
%format <$> = " "
%format <*> = " "
%format (cloAppM (x) (y)) = " " x "~:\$~" y
%format (cloLAppM (x) (y)) = " " x "~:\$^{\uparrow}~" y
%format `cloLApp` = " ~:\$^{\uparrow}~ "
%format N.Expr = " NKL "
%format (TransM (x)) = x
%format F.Expr = " FKL "
%format o = " \oplus "
%include nklQual.fmt
%include setQual.fmt
%include fklQual.fmt 
%format (ifPrimM (x) (y) (z)) = " \textbf{if}~" x "~\textbf{then}~" y "~\textbf{else}~" z
%format (opPrimM (t) (o) (x) (y)) = x o y
%format (opPrimLM (t) (o) (x) (y)) = x o"^{\uparrow}" y
%format _en = " e_{n} "
%format fvs = " \{y_1, \hdots, y_k \} "
%format (N.freeVars (e)) = " fvs~" e

\newcommand{\transform}{
\begin{code}

transform :: N.Expr            ->  TransM F.Expr
transform (N.Table t n c k)    =   pure $ F.Table t n c k
transform (N.App _t e1 e2)     =   cloAppM (transform e1) (transform e2)
transform (N.AppE1 _ p e1)     =   cloAppM (pure $ prim1Transform p) (transform e1)
transform (N.AppE2 _ p e1 e2)  =   cloAppM (cloAppM (pure $ prim2Transform p) (transform e1)) (transform e2)
transform (N.Lam t arg e)      =   do
                                    let fvs = S.toList $ N.freeVars e S.\\ S.singleton arg
                                    n' <- getFreshVar
                                    let n = F.Var (listT (Var "a")) n'
                                    cloM t n' fvs arg (transform e) (lift n e)
transform (N.If _ e1 e2 e3)    =   ifPrimM (transform e1) (transform e2) (transform e3)
transform (N.BinOp t o e1 e2)  =   opPrimM t o (transform e1) (transform e2)
transform (N.Const t v)        =   pure $ F.Const t v
transform (N.Var t x)          =   pure $ F.Var t x

\end{code}
}
\newcommand{\flatten}{
\begin{code}
lift :: F.Expr -> N.Expr -> TransM F.Expr
lift en   (N.Table t n c k)        = pure $ distPrim ((F.Table t n c k)) en
lift _en  (N.Var t x)              = pure $ F.Var (liftType t) x
lift en   (N.Const t v)            = pure $ distPrim (F.Const t v) en
lift en   (N.App _t e1 e2)         = cloLAppM (lift en e1) (lift en e2)
lift en   (N.AppE1 _ p e1)         = cloLAppM (pure $ distPrim (prim1Transform p) en) (lift en e1) 
lift en   (N.AppE2 _ p e1 e2)      = cloLAppM (cloLAppM (pure $ distPrim (prim2Transform p) en) (lift en e1)) (lift en e2)
lift en   (N.If _ e1 e2 e3)        = do
                                      e1' <- lift en e1
                                      let (F.Var t n) = en
                                      let fvs = S.toList $ N.freeVars e2 `S.union` N.freeVars e3
                                      n1' <- getFreshVar
                                      let n1 = F.Var (typeOf en) n1'
                                      n2' <- getFreshVar
                                      let n2 = F.Var (typeOf en) n2'
                                      let rt = listT $ (unliftType t) .-> typeOf e2

                                      e2' <- cloLM rt n fvs n1' (transform e2) (lift n1 e2)
                                      
                                      e3' <- cloLM rt n fvs n2' (transform e3) (lift n2 e3) 
                                      
                                      let e2'' = restrictPrim e2' e1' `cloLApp` restrictPrim en e1'
                                      let e3'' = restrictPrim e3' (notLPrim e1') `cloLApp` restrictPrim en (notLPrim e1')
                                      
                                      pure $ combinePrim e1' e2'' e3''                                                                                                                                          
lift en   (N.BinOp t o e1 e2)      = opPrimLM t o (lift en e1) (lift en e2)
lift en   (N.Lam t arg e)          = do
                                      let (F.Var _ n') = en
                                      let fvs = S.toList $ N.freeVars e S.\\ S.singleton arg
                                      cloLM (liftType t) n' fvs arg (transform e) (lift en e)
\end{code}
}