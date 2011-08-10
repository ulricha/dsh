{-# LANGUAGE TemplateHaskell #-}
module Language.ParallelLang.Translate.Detupler(normTuples, detuple) where

import Language.ParallelLang.FKL.Data.FKL as F
import Language.ParallelLang.FKL.Primitives
import Language.ParallelLang.Translate.TransM
import Language.ParallelLang.Common.Data.Type hiding (Var, Fn, Int)
import qualified Language.ParallelLang.Common.Data.Type as T
import Language.ParallelLang.Common.Data.Val
import Language.ParallelLang.Common.Data.Op

import qualified Data.List as L
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
                                                (T.Tuple ts) -> T.Tuple [transType $ T.List ty | ty <- ts]
                                                t' -> T.List t'
                        | otherwise       = ot
transType (T.Tuple ts) = let tts = map transType ts
                          in T.Tuple tts
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
                                let b = [(BinOp (listT ty) o (Proj ty 0 v1 ind) (Proj (listT ty) 0 v2 ind)) |(ind, ty) <- zip [1..] $ tupleComponents $ typeOf e1']
                                b' <- mapM deTuple b
                                return $ letF fv1 e1' $ letF fv2 e2' $ tupleF b'
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
                                      let e =  [If ty v1 (Proj ty 0 v2 ind) (Proj ty 0 v3 ind) | (ind, ty) <- zip [1..] $ tupleComponents t'] 
                                      e' <- mapM deTuple e
                                      return $ letF fv1 e1' $ letF fv2 e2' $ letF fv3 e3' $ tupleF e'
                                else return $ If t' e1' e2' e3'
deTuple (F.Tuple t es) = do
                          es' <- mapM deTuple es
                          return $ F.Tuple (transType t) es'
deTuple (Proj t l e i) = do
                            e' <- deTuple e
                            let r = Proj (transType t) l e' i
                            case e' of
                                (F.Tuple _ es) -> return $ es L.!! (i - 1)
                                _            -> return r
deTuple v@(Nil t) | containsTuple t = do
                                        let (tuple, _, _) = extractTuple t
                                        let els = tupleComponents tuple
                                        childs <- mapM deTuple [Nil $ listT e | e <- els]
                                        return $ tupleF childs
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
                                                            then Proj (head $ tupleComponents $ typeOf e2') 0 e2' 1
                                                            else e2'
                                              let v1 = Var (typeOf e1') fv1
                                              let v2 = Var (typeOf e2'') fv2
                                              eb'' <- if containsTuple $ typeOf e1'
                                                          then do
                                                                    es <- mapM deTuple [PApp3 (liftTypeN d ty) (Insert $ ty .-> typeOf v2 .-> intT .-> liftTypeN d ty) (Proj ty 0 v1 ind) v2 e3 | (ind, ty) <- zip [1..] (tupleComponents $ typeOf e1')]
                                                                    return $ tupleF es
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
                                                let ts = tupleComponents $ typeOf e2' 
                                                let v1 = Var (typeOf e1') fv1
                                                let v2 = Var (typeOf e2') fv2
                                                let v3 = Var (typeOf e3') fv3
                                                let proj2 = \x -> Proj (ts!!x) 0 v2 x
                                                let proj3 = \x -> Proj (ts!!x) 0 v3 x
                                                e' <- mapM deTuple [PApp3 t (Combine $ listT boolT .-> t .-> t .-> t) v1 (proj2 ind) (proj3 ind) | (t, ind) <- zip ts [1..]]   
                                                return $ letF fv1 e1' $
                                                            letF fv2 e2' $
                                                              letF fv3 e3' $
                                                                tupleF e'
                                         | otherwise = PApp3 rt (Insert ft) <$> deTuple e1 <*> deTuple e2 <*> deTuple e3
deTuple (PApp2 rt (Extract ft) e1 e2) | (containsTuple $ typeOf e1) && not (isFuns $ typeOf e1) =
                                            do
                                                e1' <- deTuple e1
                                                fv1 <- getFreshVar
                                                let v1 = Var (typeOf e1') fv1
                                                let ts = tupleComponents $ typeOf e1'
                                                e' <- mapM deTuple [extractF (Proj ty 0 v1 ind) e2 | (ind, ty) <- zip [1..] ts ] 
                                                return $ letF fv1 e1' $ tupleF e'
                                        | otherwise = PApp2 rt (Extract ft) <$> deTuple e1 <*> deTuple e2
deTuple (PApp2 rt (Dist ft) e1 e2) | containsTuple ft && not (isFuns rt)=
                                            do
                                                e1' <- deTuple e1
                                                e2' <- deTuple e2
                                                fv1 <- getFreshVar
                                                fv2 <- getFreshVar
                                                let e2'' = if (containsTuple $ typeOf e2') && not (isFuns $ typeOf e2')
                                                            then Proj (head $ tupleComponents $ typeOf e2') 0 e2' 1
                                                            else e2'
                                                let v1 = Var (typeOf e1') fv1
                                                let v2 = Var (typeOf e2'') fv2
                                                es <- if (containsTuple $ typeOf e1') && not (isFuns $ typeOf e1')
                                                       then
                                                        do
                                                            let ts = tupleComponents $ typeOf e1'
                                                            let rts = tupleComponents $ transType rt 
                                                            es' <- mapM deTuple [PApp2 rt' (Dist $ t .-> typeOf v2 .-> rt') (Proj t 0 v1 ident) v2 | (rt', t, ident) <- zip3 rts ts [1..]]
                                                            return $ tupleF es'
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
                                               let ts = tupleComponents $ typeOf e1'
                                               let rts = tupleComponents $ transType rt
                                               es <- mapM deTuple [PApp2 rt' (Index $ t .-> typeOf e2' .-> rt') (Proj t 0 v1 ind) v2 | (ind, t, rt') <- zip3 [1..] ts rts]
                                               return $ letF fv1 e1' $ letF fv2 e2' $ tupleF es
                                    | otherwise = PApp2 rt (Index ft) <$> deTuple e1 <*> deTuple e2
deTuple (PApp2 rt (Restrict ft) e1 e2) | containsTuple rt && not (isFuns rt) =
                                          do
                                                 e1' <- deTuple e1
                                                 e2' <- deTuple e2
                                                 fv1 <- getFreshVar
                                                 fv2 <- getFreshVar
                                                 let v1 = Var (typeOf e1') fv1
                                                 let v2 = Var (typeOf e2') fv2
                                                 let ts = tupleComponents $ typeOf e1'
                                                 let rts = tupleComponents $ transType rt
                                                 es <- mapM deTuple [PApp2 rt' (Restrict $ t .-> typeOf e2' .-> rt') (Proj t 0 v1 ind) v2 | (ind, t, rt') <- zip3 [1..] ts rts]
                                                 return $ letF fv1 e1' $ letF fv2 e2' $ tupleF es
                                       | otherwise = PApp2 rt (Restrict ft) <$> deTuple e1 <*> deTuple e2
deTuple (PApp2 rt f e1 e2) = PApp2 rt f <$> deTuple e1 <*> deTuple e2
deTuple (PApp1 rt (LengthPrim ft) e1) | (containsTuple $ typeOf e1) && not (isFuns $ typeOf e1) =  
                                            do
                                                e1' <- deTuple e1
                                                let ts = tupleComponents $ typeOf e1'
                                                deTuple $ PApp1 rt (LengthPrim $ head ts .-> intT) $ Proj (head ts) 0 e1' 1
                                      | otherwise = PApp1 rt (LengthPrim ft) <$> deTuple e1
deTuple (PApp1 rt (LengthLift ft) e1) | (containsTuple $ typeOf e1) && not (isFuns $ typeOf e1) =  
                                          do
                                              e1' <- deTuple e1
                                              let ts = tupleComponents $ typeOf e1'
                                              deTuple $ PApp1 rt (LengthLift $ head ts .-> intT) $ Proj (head ts) 0 e1' 1
                                      | otherwise = PApp1 rt (LengthLift ft) <$> deTuple e1
deTuple (PApp1 rt f e) = PApp1 rt f <$> deTuple e
deTuple (Clo t l vs x f fl) = Clo (transType t) l vs x <$> deTuple f <*> deTuple fl
deTuple (AClo t vs x f fl) = AClo (transType t) vs x <$> deTuple f <*> deTuple fl
deTuple (CloApp t f args) = CloApp (transType t) <$> deTuple f <*> deTuple args
deTuple (CloLApp t f args) = CloLApp (transType t) <$> deTuple f <*> deTuple args 
