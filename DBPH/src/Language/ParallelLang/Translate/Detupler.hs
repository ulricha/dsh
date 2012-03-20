{-# LANGUAGE TemplateHaskell, QuasiQuotes #-}
module Language.ParallelLang.Translate.Detupler(detuple) where

import Language.ParallelLang.FKL.Data.FKL as F
import Language.ParallelLang.FKL.Primitives
import Language.ParallelLang.Translate.TransM
import Language.ParallelLang.Common.Data.Type hiding (Var, Fn, Int)
import qualified Language.ParallelLang.Common.Data.Type as T
import Language.ParallelLang.Common.Data.Val (Val(Int))
import qualified Language.ParallelLang.Common.Data.Val as V
import Language.ParallelLang.Common.Data.Op

import Control.Applicative hiding (Const)
import Language.ParallelLang.Common.Impossible

detuple :: TExpr -> TransM (TExpr, Type)
detuple v = do
               e' <- deTuple v
               let (t) = transType $ typeOf v
               return (e', t)
               

transType :: Type -> Type
transType ot@(T.List t) | containsTuple t = case transType t of
                                                (T.Pair t1 t2) -> T.Pair (transType $ T.List t1) (transType $ T.List t2)
                                                t' -> T.List t'
                        | otherwise       = ot
transType (T.Pair t1 t2) = T.Pair (transType t1) (transType t2)
transType (T.Fn t1 t2)       = T.Fn (transType t1) (transType t2)
transType t                  = t

deTuple :: TExpr -> TransM TExpr
deTuple (Table t n c k) = return $ Table t n c k
deTuple (BinOp rt o e1 e2) = do
                                e1' <- deTuple e1
                                e2' <- deTuple e2
                                return $ BinOp rt o e1' e2'
deTuple (Labeled s e) = do
                          e' <- deTuple e
                          return $ Labeled s e'
deTuple (Let _ v e1 e2) = do
                            e1' <- deTuple e1
                            e2' <- deTuple e2
                            return $ Let (typeOf e2') v e1' e2'
deTuple (If t e1 e2 e3) = do
                            e1' <- deTuple e1
                            e2' <- deTuple e2
                            e3' <- deTuple e3
                            return $ If t e1' e2' e3'
deTuple (F.Pair t e1 e2) = do
                          e1' <- deTuple e1
                          e2' <- deTuple e2
                          return $ F.Pair t e1' e2'
deTuple v@(Nil _) = return v
deTuple c@(Const _ _) = return c
deTuple (Var t s)                 = return $ Var t s
deTuple (PApp3 rt (Insert ft) e1 e2 e3) | (containsTuple (typeOf e1) && not (isFuns $ typeOf e1) || containsTuple (typeOf e2)) && not (isFuns $ typeOf e2)=
                                             do
                                              e1' <- deTuple e1
                                              e2' <- deTuple e2
                                              let (Const _ (Int d)) = e3
                                              fv1 <- getFreshVar
                                              fv2 <- getFreshVar
                                              let e2'' = if containsTuple $ typeOf e2'
                                                            then fstF e2'
                                                            else e2'
                                              let v1 = Var (typeOf e1') fv1
                                              let v2 = Var (typeOf e2'') fv2
                                              eb'' <- if containsTuple $ typeOf e1'
                                                          then do
                                                                    let (t1, t2) = pairComponents $ typeOf e1'
                                                                    e1s <- deTuple $ PApp3 (liftTypeN d t1) (Insert $ t1 .-> typeOf v2 .-> intT .-> liftTypeN d t1) (fstF v1) v2 e3
                                                                    e2s <- deTuple $ PApp3 (liftTypeN d t2) (Insert $ t2 .-> typeOf v2 .-> intT .-> liftTypeN d t2) (sndF v1) v2 e3
                                                                    return $ pairF e1s e2s
                                                          else deTuple $ PApp3 rt (Insert $ typeOf e1' .-> typeOf v2 .-> intT .-> rt) v1 v2 e3
                                              return $ letF fv1 e1' $ letF fv2 e2'' eb''
                                         | otherwise = PApp3 rt (Insert ft) <$> deTuple e1 <*> deTuple e2 <*> deTuple e3
deTuple (PApp3 rt f e1 e2 e3) = PApp3 rt f <$> deTuple e1 <*> deTuple e2 <*> deTuple e3
deTuple (PApp2 rt (Extract ft) e1 e2)  = PApp2 rt (Extract ft) <$> deTuple e1 <*> deTuple e2
deTuple (PApp2 rt (Dist ft) e1 e2) {- | containsTuple ft && not (isFuns rt) =
                                            do
                                                e1' <- deTuple e1
                                                e2' <- deTuple e2
                                                fv1 <- getFreshVar
                                                fv2 <- getFreshVar
                                                let e2'' = if (containsTuple $ typeOf e2') && not (isFuns $ typeOf e2')
                                                            then fstF e2'
                                                            else e2'
                                                let v1 = Var (typeOf e1') fv1
                                                let v2 = Var (typeOf e2'') fv2
                                                es <- if (containsTuple $ typeOf e1') && not (isFuns $ typeOf e1')
                                                       then
                                                        do
                                                            let (t1, t2) = pairComponents $ typeOf e1'
                                                            let (rt1, rt2) = pairComponents $ transType rt 
                                                            e1s <- deTuple $ PApp2 rt1 (Dist $ t1 .-> typeOf v2 .-> rt1) (fstF v1) v2
                                                            e2s <- deTuple $ PApp2 rt2 (Dist $ t2 .-> typeOf v2 .-> rt2) (sndF v1) v2
                                                            return $ pairF e1s e2s
                                                       else
                                                        do
                                                            return $ PApp2 rt (Dist $ typeOf v1 .-> typeOf v2 .-> listT (typeOf v1)) v1 v2
                                                e' <- deTuple es
                                                return $ letF fv1 e1' $ letF fv2 e2'' e' -}
                                     | otherwise = PApp2 rt (Dist ft) <$> deTuple e1 <*> deTuple e2
deTuple (PApp2 rt (Index ft) e1 e2)  = PApp2 rt (Index ft) <$> deTuple e1 <*> deTuple e2
deTuple (PApp2 rt f e1 e2) = PApp2 rt f <$> deTuple e1 <*> deTuple e2
deTuple (PApp1 rt f e) = PApp1 rt f <$> deTuple e
deTuple (Clo t l vs x f fl) = Clo (transType t) l vs x <$> deTuple f <*> deTuple fl
deTuple (AClo t n e vs x f fl) = AClo (transType t) n <$> deTuple e <*> pure vs <*> pure x <*> deTuple f <*> deTuple fl
deTuple (CloApp t f args) = CloApp (transType t) <$> deTuple f <*> deTuple args
deTuple (CloLApp t f args) = CloLApp (transType t) <$> deTuple f <*> deTuple args 
