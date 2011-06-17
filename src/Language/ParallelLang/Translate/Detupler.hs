{-# LANGUAGE TemplateHaskell #-}
module Language.ParallelLang.Translate.Detupler(normTuples, detuple) where

import Language.ParallelLang.Common.Impossible

import Language.ParallelLang.FKL.Data.FKL as F
import Language.ParallelLang.FKL.Data.WorkUnits as W
import Language.ParallelLang.FKL.Primitives
import Language.ParallelLang.Translate.TransM
import Language.ParallelLang.Common.Data.Type hiding (Var, Fn)
import qualified Language.ParallelLang.Common.Data.Type as T
import Language.ParallelLang.Common.Data.Val
import Language.ParallelLang.Common.Data.Op

import qualified Data.List as L
import Control.Applicative hiding (Const)

detuple :: TExpr -> TransM (TExpr, ReconstructionPlan)
detuple v = do
               e' <- normTuples v
               return (e', snd $ transType $ typeOf v)
               

normTuples :: TExpr -> TransM TExpr
normTuples e = do
                        e' <- deTuple e
                        return e'
                        
transType :: Type -> (Type, ReconstructionPlan)
transType ot@(T.TyC "List" [t]) | containsTuple t = let (TyC "tuple" ts, f) = transType t
                                                     in (TyC "tuple" [TyC "List" [ty] | ty <- ts], Compose (Map f) Zip)
                                | otherwise       = (ot, Id)
transType (T.TyC "tuple" ts) = let tts = map transType ts
                                in (T.TyC "tuple" $ map fst tts, W.Tuple $ map snd tts)
transType (T.Fn t1 t2)       = (T.Fn (fst $ transType t1) (fst $ transType t2), error "Cannot make reconstruction plan for function types")
transType t                  = (t, Id)

deTuple :: TExpr -> TransM TExpr
deTuple (BinOp rt o@(Op ":" _) e1 e2) | containsTuple rt =
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
                            let t' = fst $ transType t
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
                          return $ F.Tuple (fst $ transType t) es'
deTuple (Proj t l e i) = do
                            e' <- deTuple e
                            let r = Proj (fst $ transType t) l e' i
                            case e' of
                                (F.Tuple _ es) -> return $ es L.!! (i - 1)
                                _            -> return r
deTuple v@(Nil t) | containsTuple t = do
                                        let (tuple, _, _) = extractTuple t
                                        let els = tupleComponents tuple
                                        childs <- mapM deTuple [Nil e | e <- els]
                                        return $ tupleF childs
                  | otherwise       = return v
deTuple c@(Const _ _)               = return c
deTuple (Var t s)                 = return $ Var (fst $ transType t) s
deTuple a@(App rt (Var ft n) [e1 ,e2, e3])   | n == "insert" && (containsTuple (typeOf e1) || containsTuple (typeOf e2)) =
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
                                                                            es <- mapM deTuple [App (liftTypeN d ty) (Var (ty .-> typeOf v2 .-> intT .-> liftTypeN d ty) "insert") [Proj ty 0 v1 ind, v2, e3] | (ind, ty) <- zip [1..] (tupleComponents $ typeOf e1')]
                                                                            return $ tupleF es
                                                                  else deTuple $ App rt (Var (typeOf e1' .-> typeOf v2 .-> intT .-> rt) "insert") [v1, v2, e3]
                                                      return $ letF fv1 e1' $ letF fv2 e2'' eb''
                                                | n == "combine" && containsTuple rt = 
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
                                                        e' <- mapM deTuple [App t (Var (listT boolT .-> t .-> t .-> t) n) [v1, proj2 ind, proj3 ind] | (t, ind) <- zip ts [1..]]   
                                                        return $ letF fv1 e1' $
                                                                    letF fv2 e2' $
                                                                      letF fv3 e3' $
                                                                        tupleF e'                                                                            
                                               | not $ containsTuple ft = return a
                                               | otherwise = deTupleApp a
deTuple a@(App rt (Var ft n) [e1 ,e2])      | n == "extract" && (containsTuple $ typeOf e1) =
                                                    do
                                                        e1' <- deTuple e1
                                                        fv1 <- getFreshVar
                                                        let v1 = Var (typeOf e1') fv1
                                                        let ts = tupleComponents $ typeOf e1'
                                                        e' <- mapM deTuple [extractF (Proj ty 0 v1 ind) e2 | (ind, ty) <- zip [1..] ts ] 
                                                        return $ letF fv1 e1' $ tupleF e'
                                               | n == "dist" && (containsTuple ft) = 
                                                    do
                                                        e1' <- deTuple e1
                                                        e2' <- deTuple e2
                                                        fv1 <- getFreshVar
                                                        fv2 <- getFreshVar
                                                        let e2'' = if containsTuple $ typeOf e2'
                                                                    then Proj (head $ tupleComponents $ typeOf e2') 0 e2' 1
                                                                    else e2'
                                                        let v1 = Var (typeOf e1') fv1
                                                        let v2 = Var (typeOf e2'') fv2
                                                        es <- if containsTuple $ typeOf e1' 
                                                               then
                                                                do
                                                                    let ts = tupleComponents $ typeOf e1'
                                                                    let rts = tupleComponents $ fst $ transType rt 
                                                                    es' <- mapM deTuple [App rt' (Var (t .-> typeOf v2 .-> rt') n) [(Proj t 0 v1 ident), v2] | (rt', t, ident) <- zip3 rts ts [1..]]
                                                                    return $ tupleF es'
                                                               else
                                                                do
                                                                    return $ App rt (Var (typeOf v1 .-> typeOf v2 .-> listT (typeOf v1)) n) [v1, v2]
                                                        e' <- deTuple es
                                                        return $ letF fv1 e1' $ letF fv2 e2'' e'
                                            | n `elem` ["index", "restrict"] && containsTuple ft =
                                                   do
                                                       e1' <- deTuple e1
                                                       e2' <- deTuple e2
                                                       fv1 <- getFreshVar
                                                       fv2 <- getFreshVar
                                                       let v1 = Var (typeOf e1') fv1
                                                       let v2 = Var (typeOf e2') fv2
                                                       let ts = tupleComponents $ typeOf e1'
                                                       let rts = tupleComponents $ fst $ transType rt
                                                       es <- mapM deTuple [App rt' (Var (t .-> typeOf e2' .-> rt') n) [(Proj t 0 v1 ind), v2] | (ind, t, rt') <- zip3 [1..] ts rts]
                                                       return $ letF fv1 e1' $ letF fv2 e2' $ tupleF es
                                            | n == "promote" && (containsTuple $ typeOf e2) =
                                                    do
                                                        let t2 = typeOf e2
                                                        let (t2', _) = transType t2
                                                        let k = listDepth t2
                                                        e1' <- deTuple e1
                                                        e2' <- deTuple e2 
                                                        fv2 <- getFreshVar
                                                        let v2 = Var (head $ tupleComponents t2') fv2
                                                        let e2h = Proj (head $ tupleComponents t2') 0 e2' 1
                                                        bd <- deTuple $ insertF (distF e1' $ extractF v2 (intF $ k - 1)) v2 (intF $ k - 1)
                                                        return $ letF fv2 e2h bd 
                                            | not (containsTuple ft) = return a
                                            | otherwise = deTupleApp a
deTuple a@(App rt (Var ft n) [e1]) | n == "length" && (containsTuple $ typeOf e1) =
                                                    do
                                                        e1' <- deTuple e1
                                                        let ts = tupleComponents $ typeOf e1'
                                                        deTuple $ App rt (Var (head ts .-> intT) n) [Proj (head ts) 0 e1' 1]
                                      | not (containsTuple ft) = return a
                                      | otherwise   = deTupleApp a
deTuple a@(App _ (Var ft _ ) _) | not (containsTuple ft) = return a
                                 | otherwise = deTupleApp a
deTuple (App _ _ _) = $impossible
deTuple (Lam t arg e) = do
                          e' <- deTuple e
                          let t' = fst $ transType t
                          return $ Lam t' arg e'
deTuple (Clo t l vs x f fl) = Clo (fst $ transType t) l vs x <$> deTuple f <*> deTuple fl
deTuple (AClo t vs x f fl) = AClo (fst $ transType t) vs x <$> deTuple f <*> deTuple fl
deTuple (CloApp t f args) = CloApp (fst $ transType t) <$> deTuple f <*> deTuple args
deTuple (CloLApp t f args) = CloLApp (fst $ transType t) <$> deTuple f <*> deTuple args 


deTupleApp :: TExpr -> TransM TExpr
deTupleApp (App rt e1 es) = do
                             let rt' = fst $ transType rt
                             e1' <- deTuple e1
                             es' <- mapM deTuple es
                             return $ App rt' e1' es'
deTupleApp _             = $impossible
