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
deTuple (PApp3 rt f e1 e2 e3) = PApp3 rt f <$> deTuple e1 <*> deTuple e2 <*> deTuple e3
deTuple (PApp2 rt f e1 e2) = PApp2 rt f <$> deTuple e1 <*> deTuple e2
deTuple (PApp1 rt f e) = PApp1 rt f <$> deTuple e
deTuple (Clo t l vs x f fl) = Clo t l vs x <$> deTuple f <*> deTuple fl
deTuple (AClo t n e vs x f fl) = AClo t n <$> deTuple e <*> pure vs <*> pure x <*> deTuple f <*> deTuple fl
deTuple (CloApp t f args) = CloApp t <$> deTuple f <*> deTuple args
deTuple (CloLApp t f args) = CloLApp t <$> deTuple f <*> deTuple args 
