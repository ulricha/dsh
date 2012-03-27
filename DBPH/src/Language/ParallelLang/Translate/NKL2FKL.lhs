%if False
\begin{code}
{-# LANGUAGE TemplateHaskell, TupleSections #-}
module Language.ParallelLang.Translate.NKL2FKL (flatTransform) where

import qualified Language.ParallelLang.FKL.Data.FKL as F
import qualified Language.ParallelLang.NKL.Data.NKL as N
import Language.ParallelLang.Common.Data.Op
import Language.ParallelLang.Translate.TransM

import Language.ParallelLang.FKL.Primitives
import Language.ParallelLang.Common.Data.Type

import qualified Data.Set as S

import Control.Applicative

flatTransform :: N.Expr -> TransM F.Expr
flatTransform = withCleanClosureEnv . transform 

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

\newcommand{\transform}{
\begin{code}

transform :: N.Expr -> TransM F.Expr
transform (N.Table t n c k)    = pure $ F.Table t n c k
transform (N.App _t e1 es)     = cloApp <$> transform e1 <*> transform es
transform (N.AppE1 _ p e1)     = cloApp (prim1Transform p) <$> transform e1
transform (N.AppE2 _ p e1 e2)  = cloApp <$> (cloApp (prim2Transform p) <$> transform e1) <*> transform e2
transform (N.Lam t arg e)      = do
                                  let fvs = S.toList $ N.freeVars e S.\\ S.singleton arg
                                  n' <- getFreshVar
                                  let n = F.Var (listT (Var "a")) n'
                                  e' <- withClosure (arg:fvs) $ lift n e
                                  e'' <- transform e
                                  pure $ F.Clo t n' fvs arg e'' e'
transform (N.If t e1 e2 e3)    = F.If t <$> transform e1 <*> transform e2 <*> transform e3
transform (N.BinOp t o e1 e2)  = F.BinOp t (Op o False) <$> transform e1 <*> transform e2
transform (N.Const t v)        = pure $ F.Const t v
transform (N.Var t x)          = pure $ F.Var t x
\end{code}
}
\newcommand{\flatten}{
\begin{code}
lift :: F.Expr -> N.Expr -> TransM F.Expr
lift en   (N.Table t n c k) = return $ distPrim (F.Table t n c k) en
lift _en  (N.Var t x) = return $ F.Var (liftType t) x
lift en   (N.Const t v) = return $ distPrim (F.Const t v) en
lift en   (N.App _t f es) = cloLApp <$> lift en f <*> lift en es
lift en   (N.AppE1 _ p arg) = cloLApp (distPrim (prim1Transform p) en) <$> lift en arg 
lift en   (N.AppE2 _ p arg1 arg2) = cloLApp <$> (cloLApp (distPrim (prim2Transform p) en) <$> lift en arg1) <*> lift en arg2
lift en   (N.If _ e1 e2 e3) = do
                                   e1' <- lift en e1
                                   let (F.Var t n) = en
                                   -- let r1 = restrictPrim en e1'
                                   -- let r2 = restrictPrim en (notLPrim e1')
                                   let fvs = S.toList $ N.freeVars e2 `S.union` N.freeVars e3
                                   n1' <- getFreshVar
                                   let n1 = F.Var (typeOf en) n1'
                                   n2' <- getFreshVar
                                   let n2 = F.Var (typeOf en) n2'
                                   let rt = listT $ (unliftType t) .-> typeOf e2
                                   e21 <- withCleanClosureEnv $ transform e2
                                   
                                   e22 <- withClosure (n1':fvs) (lift n1 e2) 
                                   let e2' = F.AClo rt n fvs n1' e21 e22
                                   
                                   e31 <- withCleanClosureEnv $ transform e3
                                   e32 <- withClosure (n1':fvs) (lift n2 e3)
                                   let e3' = F.AClo rt n fvs n2' e31 e32
                                   
                                   let e2'' = restrictPrim e2' e1'
                                   let e3'' = restrictPrim e3' (notLPrim e1')
                                   
                                   return $ combinePrim e1' (e2'' `cloLApp` en) (e3'' `cloLApp` en)                                                                                                                                          
                                   {- e2' <- lift r1 e2
                                   e3' <- lift r2 e3
                                   return $ combinePrim e1' e2' e3' -}
                                   {- r1' <- getFreshVar
                                   r2' <- getFreshVar 
                                   v1' <- getFreshVar
                                   v2' <- getFreshVar
                                   v3' <- getFreshVar
                                   e1' <- lift en e1
                                   let v1 = F.Var (typeOf e1') v1'
                                   let rv1 = restrictPrim en v1
                                   let r1 = F.Var (typeOf rv1) r1'
                                   e2' <- lift r1 e2
                                   let rv2 = restrictPrim en (notLPrim v1)
                                   let r2 = F.Var (typeOf rv2) r2'
                                   e3' <- lift r2 e3
                                   let v2 = F.Var (typeOf e2') v2'
                                   let v3 = F.Var (typeOf e3') v3'
                                   return $ letF v1' e1' $ letF r1' rv1 $ letF r2' rv2 $ letF v2' e2' $ letF v3' e3' $ combinePrim v1 v2 v3 -}
lift en   (N.BinOp t o e1 e2) = (F.BinOp (liftType t) (Op o True)) <$> lift en e1 <*> lift en e2
lift en   (N.Lam t arg e) = do
                                let (F.Var _ n') = en
                                e' <- withCleanClosureEnv $ transform e
                                let fvs = S.toList $ N.freeVars e S.\\ S.singleton arg
                                e'' <- withClosure (arg:fvs) (lift en e)
                                return $ F.AClo (liftType t) n' fvs arg e' e''
\end{code}}