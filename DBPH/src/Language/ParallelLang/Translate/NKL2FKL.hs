{-# LANGUAGE TemplateHaskell #-}
module Language.ParallelLang.Translate.NKL2FKL (flatTransform) where

import qualified Language.ParallelLang.FKL.Data.FKL as F
import qualified Language.ParallelLang.NKL.Data.NKL as N
import Language.ParallelLang.Common.Data.Op
import Language.ParallelLang.Translate.TransM

import Language.ParallelLang.FKL.Primitives
import Language.ParallelLang.Common.Impossible
import Language.ParallelLang.Common.Data.Type

import qualified Data.Set as S

import Control.Applicative

flatTransform :: N.Expr -> TransM F.Expr
flatTransform e = do
                    e' <- withCleanLetEnv $ transform e
                    return e'

transEnv :: [(String, N.Expr)] -> TransM [(String, F.Expr)]
transEnv ((x, v):xs) = do
                        v' <- transform v
                        xs' <- transEnv xs
                        return ((x, v'):xs')
transEnv []          = return []

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

transform :: N.Expr -> TransM F.Expr
transform (N.Table t n c k) = pure $ F.Table t n c k
transform (N.App _t e1 es) = cloApp <$> transform e1 <*> transform es
transform (N.AppE1 _ p e1) = cloApp (prim1Transform p) <$> transform e1
transform (N.AppE2 _ p e1 e2) = cloApp <$> (cloApp (prim2Transform p) <$> transform e1) <*> transform e2
transform (N.Lam t arg e) = do
                             fvs <- transEnv $ S.toList $ N.freeVars (arg:topLevelVars) e
                             i' <- getFreshVar
                             n' <- getFreshVar
                             let n = F.Var (listT (Var "a")) n'
                             e' <- foldr withLetVar (flatten i' n e) (arg: map fst fvs)
                             e'' <- transform e
                             return $ F.Clo t n' fvs arg e'' e'
transform (N.If t e1 e2 e3) = F.If t <$> transform e1 <*> transform e2 <*> transform e3
transform (N.BinOp t o e1 e2) = F.BinOp t o <$> transform e1 <*> transform e2
transform (N.Const t v) = pure $ F.Const t v
transform (N.Var t x) = pure $ F.Var t x

flatten :: String -> F.Expr -> N.Expr -> TransM F.Expr
flatten _ e1 (N.Table t n c k) = return $ distF (F.Table t n c k) e1
flatten _ e1 (N.Var t x) | x `elem` topLevelVars = return $ distF (F.Var t x) e1
                         | otherwise             = return $ F.Var (liftType t) x
flatten _ e1 (N.Const t v) = return $ distF (F.Const t v) e1
flatten i e1 (N.App _t f es) = cloLApp <$> flatten i e1 f <*> flatten i e1 es
flatten i e1 (N.AppE1 _ p arg) = cloLApp (distF (prim1Transform p) e1) <$> flatten i e1 arg 
flatten i e1 (N.AppE2 _ p arg1 arg2) = cloLApp <$> (cloLApp (distF (prim2Transform p) e1) <$> flatten i e1 arg1) <*> flatten i e1 arg2
flatten i d (N.If _ e1 e2 e3) = do
                                    r1' <- getFreshVar
                                    r2' <- getFreshVar 
                                    v1' <- getFreshVar
                                    v2' <- getFreshVar
                                    v3' <- getFreshVar
                                    e1' <- flatten i d e1
                                    let v1 = F.Var (typeOf e1') v1'
                                    let rv1 = restrictF d v1
                                    let r1 = F.Var (typeOf rv1) r1'
                                    e2' <- flatten i r1 e2
                                    let rv2 = restrictF d (notF v1)
                                    let r2 = F.Var (typeOf rv2) r2'
                                    e3' <- flatten i r2 e3
                                    let v2 = F.Var (typeOf e2') v2'
                                    let v3 = F.Var (typeOf e3') v3'
                                    return $ letF v1' e1' $ letF r1' rv1 $ letF r2' rv2 $ letF v2' e2' $ letF v3' e3' $ combineF v1 v2 v3
flatten i d (N.BinOp t (Op o False) e1 e2) = do
                                    (F.BinOp (liftType t) (Op o True)) <$> flatten i d e1 <*> flatten i d e2
flatten _ _ (N.BinOp _ _ _ _) = $impossible
flatten v d (N.Lam t arg e) = do
                                i' <- getFreshVar
                                n' <- getFreshVar
                                let n = F.Var (typeOf d) n'
                                e' <- withCleanLetEnv $ transform e
                                fvs <- transEnv $ S.toList $ N.freeVars (arg:topLevelVars) e
                                e'' <- withCleanLetEnv $ foldr withLetVar (flatten i' n e) (arg: map fst fvs)
                                return $ letF v d $ F.AClo (liftType t) n' d fvs arg e' e''

topLevelVars :: [String]
topLevelVars = ["dist", "restrict", "combine", "not", "insert", "extract", "map", "length"]

