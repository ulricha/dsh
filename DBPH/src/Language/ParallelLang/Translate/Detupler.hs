{-# LANGUAGE TemplateHaskell #-}
module Language.ParallelLang.Translate.Detupler(normTuples, detuple) where

import Language.ParallelLang.FKL.Data.FKL as F
import Language.ParallelLang.FKL.Primitives
import Language.ParallelLang.Translate.TransM
import Language.ParallelLang.Common.Data.Type hiding (Var, Fn, Int)
import qualified Language.ParallelLang.Common.Data.Type as T
import Language.ParallelLang.Common.Data.Val
import Language.ParallelLang.Common.Data.Op

import Control.Applicative hiding (Const)

detuple :: TExpr -> TransM (TExpr, Type)
detuple v = do
               e' <- normTuples v
               let (t) = transType $ typeOf v
               return (e', t)
               

normTuples :: TExpr -> TransM TExpr
normTuples e = do
                        e' <- deTuple e
                        return e'
                        
transType :: Type -> Type
transType ot@(T.List t) | containsTuple t = case transType t of
                                                (T.Pair t1 t2) -> T.Pair (transType $ T.List t1) (transType $ T.List t2)
                                                t' -> T.List t'
                        | otherwise       = ot
transType (T.Pair t1 t2) = T.Pair (transType t1) (transType t2)
transType (T.Fn t1 t2)       = T.Fn (transType t1) (transType t2)
transType t                  = t

deTuple :: TExpr -> TransM TExpr
deTuple (Table t n c k) = return $ Table (transType t) n c k
deTuple (BinOp rt o@(Op Cons _) e1 e2) | containsTuple rt =
                            do
                                e1' <- deTuple e1
                                e2' <- deTuple e2
                                fv1 <- getFreshVar
                                fv2 <- getFreshVar
                                let v1 = Var (typeOf e1') fv1
                                let v2 = Var (typeOf e2') fv2
                                let (t1, t2) = pairComponents $ typeOf e1'
                                e1'' <- deTuple $ (BinOp (listT t1) o (fstF v1) (fstF v2))
                                e2'' <- deTuple $ (BinOp (listT t2) o (sndF v1) (sndF v2))
                                return $ letF fv1 e1' $ letF fv2 e2' $ pairF e1'' e2''
                                      | otherwise =
                            do
                                e1' <- deTuple e1
                                e2' <- deTuple e2
                                return (BinOp rt o e1' e2')
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
                            let t' = transType t
                            if containsTuple t'
                                then do
                                      fv1 <- getFreshVar
                                      fv2 <- getFreshVar
                                      fv3 <- getFreshVar
                                      let v1 = Var (typeOf e1') fv1
                                      let v2 = Var (typeOf e2') fv2
                                      let v3 = Var (typeOf e3') fv3
                                      let (t1, t2) = pairComponents t'
                                      e1'' <- deTuple $ If t1 v1 (fstF v2) (fstF v3)
                                      e2'' <- deTuple $ If t2 v1 (sndF v2) (sndF v3)
                                      return $ letF fv1 e1' $ letF fv2 e2' $ letF fv3 e3' $ pairF e1'' e2''
                                else return $ If t' e1' e2' e3'
deTuple (F.Pair t e1 e2) = do
                          e1' <- deTuple e1
                          e2' <- deTuple e2
                          return $ F.Pair (transType t) e1' e2'
deTuple v@(Nil t) | containsTuple t = do
                                        let tuple = extractPair t
                                        let (t1, t2) = pairComponents tuple
                                        c1 <- deTuple $ Nil (listT t1)
                                        c2 <- deTuple $ Nil (listT t2)
                                        return $ pairF c1 c2
                  | otherwise       = return v
deTuple c@(Const _ _)               = return c
deTuple (Var t s)                 = return $ Var (transType t) s
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
deTuple (PApp3 rt (Combine ft) e1 e2 e3) | containsTuple rt && not (isFuns rt)=
                                            do
                                                e1' <- deTuple e1
                                                e2' <- deTuple e2
                                                e3' <- deTuple e3
                                                fv1 <- getFreshVar
                                                fv2 <- getFreshVar
                                                fv3 <- getFreshVar
                                                let (t1, t2) = pairComponents $ typeOf e2' 
                                                let v1 = Var (typeOf e1') fv1
                                                let v2 = Var (typeOf e2') fv2
                                                let v3 = Var (typeOf e3') fv3
                                                e1'' <- deTuple $ PApp3 t1 (Combine $ listT boolT .-> t1 .-> t1 .-> t1) v1 (fstF v2) (fstF v3)
                                                e2'' <- deTuple $ PApp3 t2 (Combine $ listT boolT .-> t2 .-> t2 .-> t2) v1 (sndF v2) (sndF v3)
                                                return $ letF fv1 e1' $
                                                            letF fv2 e2' $
                                                              letF fv3 e3' $
                                                                pairF e1'' e2''
                                         | otherwise = PApp3 rt (Insert ft) <$> deTuple e1 <*> deTuple e2 <*> deTuple e3
deTuple (PApp2 rt (Extract ft) e1 e2) | (containsTuple $ typeOf e1) && not (isFuns $ typeOf e1) =
                                            do
                                                e1' <- deTuple e1
                                                fv1 <- getFreshVar
                                                let v1 = Var (typeOf e1') fv1
                                                e1'' <- deTuple $ extractF (fstF v1) e2
                                                e2'' <- deTuple $ extractF (sndF v1) e2
                                                return $ letF fv1 e1' $ pairF e1'' e2''
                                        | otherwise = PApp2 rt (Extract ft) <$> deTuple e1 <*> deTuple e2
deTuple (PApp2 rt (Dist ft) e1 e2) | containsTuple ft && not (isFuns rt)=
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
                                                return $ letF fv1 e1' $ letF fv2 e2'' e'
                                     | otherwise = PApp2 rt (Dist ft) <$> deTuple e1 <*> deTuple e2
deTuple (PApp2 rt (Index ft) e1 e2) | containsTuple rt && not (isFuns rt) =
                                        do
                                               e1' <- deTuple e1
                                               e2' <- deTuple e2
                                               fv1 <- getFreshVar
                                               fv2 <- getFreshVar
                                               let v1 = Var (typeOf e1') fv1
                                               let v2 = Var (typeOf e2') fv2
                                               let (t1, t2) = pairComponents $ typeOf e1'
                                               let (rt1, rt2) = pairComponents $ transType rt
                                               e1'' <- deTuple $ PApp2 rt1 (Index $ t1 .-> typeOf e2' .-> rt1) (fstF v1) v2
                                               e2'' <- deTuple $ PApp2 rt2 (Index $ t2 .-> typeOf e2' .-> rt2) (sndF v1) v2
                                               return $ letF fv1 e1' $ letF fv2 e2' $ pairF e1'' e2''
                                    | otherwise = PApp2 rt (Index ft) <$> deTuple e1 <*> deTuple e2
deTuple (PApp2 rt (Restrict ft) e1 e2) | containsTuple rt && not (isFuns rt) =
                                          do
                                                 e1' <- deTuple e1
                                                 e2' <- deTuple e2
                                                 fv1 <- getFreshVar
                                                 fv2 <- getFreshVar
                                                 let v1 = Var (typeOf e1') fv1
                                                 let v2 = Var (typeOf e2') fv2
                                                 let (t1, t2) = pairComponents $ typeOf e1'
                                                 let (rt1, rt2) = pairComponents $ transType rt
                                                 e1'' <- deTuple $ PApp2 rt1 (Restrict $ t1 .-> typeOf e2' .-> rt1) (fstF v1) v2
                                                 e2'' <- deTuple $ PApp2 rt2 (Restrict $ t2 .-> typeOf e2' .-> rt2) (sndF v1) v2
                                                 return $ letF fv1 e1' $ letF fv2 e2' $ pairF e1'' e2''
                                       | otherwise = PApp2 rt (Restrict ft) <$> deTuple e1 <*> deTuple e2
deTuple (PApp2 rt f e1 e2) = PApp2 rt f <$> deTuple e1 <*> deTuple e2
deTuple (PApp1 rt (LengthPrim ft) e1) | (containsTuple $ typeOf e1) && not (isFuns $ typeOf e1) =  
                                            do
                                                e1' <- deTuple e1
                                                let (t1, _) = pairComponents $ typeOf e1'
                                                deTuple $ PApp1 rt (LengthPrim $ t1 .-> intT) $ fstF e1'
                                      | otherwise = PApp1 rt (LengthPrim ft) <$> deTuple e1
deTuple (PApp1 rt (LengthLift ft) e1) | (containsTuple $ typeOf e1) && not (isFuns $ typeOf e1) =  
                                          do
                                              e1' <- deTuple e1
                                              let (t1, _) = pairComponents $ typeOf e1'
                                              deTuple $ PApp1 rt (LengthLift $ t1 .-> intT) $ fstF e1'
                                      | otherwise = PApp1 rt (LengthLift ft) <$> deTuple e1
deTuple (PApp1 _ (Fst _) e) = do
                            e' <- deTuple e
                            case e' of
                                (F.Pair _ e1 _) -> return e1
                                _               -> return $ fstF e'
deTuple (PApp1 _ (Snd _) e) = do
                            e' <- deTuple e
                            case e' of
                                (F.Pair _ _ e2) -> return e2
                                _               -> return $ sndF e'
deTuple (PApp1 _ (FstL _) e) = do
                                  e' <- deTuple e
                                  case e' of
                                      (F.Pair _ e1 _) -> return e1
                                      _               -> return $ fstF e'
deTuple (PApp1 _ (SndL _) e) = do
                                e' <- deTuple e
                                case e' of
                                    (F.Pair _  _ e2) -> return e2
                                    _               -> return $ sndF e'
deTuple (PApp1 rt f e) = PApp1 rt f <$> deTuple e
deTuple (Clo t l vs x f fl) = Clo (transType t) l vs x <$> deTuple f <*> deTuple fl
deTuple (AClo t vs x f fl) = AClo (transType t) vs x <$> deTuple f <*> deTuple fl
deTuple (CloApp t f args) = CloApp (transType t) <$> deTuple f <*> deTuple args
deTuple (CloLApp t f args) = CloLApp (transType t) <$> deTuple f <*> deTuple args 
