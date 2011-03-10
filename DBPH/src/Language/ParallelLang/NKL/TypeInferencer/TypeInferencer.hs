{-# LANGUAGE TypeSynonymInstances, GeneralizedNewtypeDeriving, StandaloneDeriving, MultiParamTypeClasses, FlexibleInstances, TemplateHaskell #-}
module Language.ParallelLang.NKL.TypeInferencer.TypeInferencer where
    
import qualified Language.ParallelLang.NKL.Data.NKL as Ty
import qualified Language.ParallelLang.NKL.Data.UntypedNKL as U
import Language.ParallelLang.NKL.TypeInferencer.Types
import Language.ParallelLang.Common.Data.Type
import Language.ParallelLang.NKL.TypeInferencer.Unification
import Language.ParallelLang.Common.Data.Val
import Language.ParallelLang.Common.Data.Op

import Control.Applicative hiding (Const(..))

algW :: ([U.Expr], U.Expr) -> AlgW ([Ty.Expr], Ty.Expr)
algW ((f@(U.Fn n _ _ _ _):fs), e) = 
                  do
                    f' <- typeFunction f
                    let t = generalise $ typeOf f'
                    (fs', e') <- addToEnv n t $ algW (fs, e)
                    return (f':fs', e')
algW (_:_, _) = error "Expected a function"
algW ([], e) = do
                e' <- typeExpr e
                return ([], e')

splitType :: [String] -> Type -> ([(String, Type)], Type)
splitType (x:xs) (Fn t1 t2) = let (ts, rt) = splitType xs t2
                               in ((x, t1):ts, rt)
splitType []     t          = ([], t)
splitType _ _               = error "The number of arguments doesn't match the type given for this function"

infix .<.

(.<.) :: Type -> Type -> AlgW Bool
t1 .<. t2 = do
              (r, _) <- instanceOf t1 t2 []
              return r

instanceOf :: Type -> Type -> [String] -> AlgW (Bool, [String])
instanceOf t t2@(Var v) vs = if v `elem` vs
                                    then if t == t2 then return (True, vs)
                                                    else return (False, vs)
                                    else do
                                            updateSubstitution v t
                                            return (True, vs ++ varsInType t)
instanceOf (Var _) _ vs = return (False, vs)
instanceOf (Fn t1 t2) (Fn t3 t4) vs = do
                                    (r1, vs') <- instanceOf t1 t3 vs
                                    if r1 
                                     then
                                         do
                                             t4' <- applyS (pure t4)
                                             instanceOf t2 t4' vs'
                                     else
                                         return (False, vs')
instanceOf (TyC c1 (t1:ts1)) (TyC c2 (t2:ts2)) vs | c1 == c2 =
                             do
                                (r1, vs') <- instanceOf t1 t2 vs
                                if r1
                                 then
                                     do
                                         ts2' <- sequence $ map applyS (map pure ts2)
                                         instanceOf (TyC c1 ts1) (TyC c2 ts2') vs'
                                 else return (r1, vs')
                                                  | otherwise = return (False, vs)
instanceOf (TyC c1 [])  (TyC c2 []) vs | c1 == c2  = return (True, vs)    
                                       | otherwise = return (False, vs)
instanceOf _            _           vs = return (False, vs)
                                
                                
    
typeFunction :: U.Expr -> AlgW Ty.Expr
typeFunction (U.Fn n i args e Nothing) = do -- have to exploit the knowledge about liftedness
                                fvs <- mapM (const freshTyVar) args
                                let binds = zip args fvs
                                e' <- foldr (\(x,t) m -> addToEnv x (Ty $ Var t) m) (typeExpr e) binds 
                                let bt = typeOf e'
                                let ft = foldr (.->) bt (map Var fvs)
                                ft' <- applyS (pure ft)
                                return $ Ty.Fn ft' n i args e'
typeFunction (U.Fn n i args e (Just t)) = do
                                            gt <- instantiate $ generalise t
                                            let (ts, _) = splitType args gt
                                            e' <- foldr (\(x,xt) m -> addToEnv x (Ty $ xt) m) (typeExpr e) ts
                                            let bt = typeOf e'
                                            let ft = foldr (.->) bt (map snd ts)
                                            ft' <- applyS (pure ft)
                                            b <- gt .<. ft'
                                            if b then
                                                    applyS $ pure $ Ty.Fn ft' n i args e'
                                                 else
                                                     fail $ "Inferred type doesn't match expected type:\n"
                                                                ++ "Inferred: " ++ show ft'
                                                                ++ "\nExpected: " ++ show t 
typeFunction _ = error "Can't type this declaration, not a function"

typeExpr :: U.Expr -> AlgW Ty.Expr
typeExpr (U.Typed e t) = do
                            t' <- instantiate $ generalise t
                            e' <- typeExpr e
                            b <- t' .<. (typeOf e')
                            if b
                                then applyS $ pure e'
                                else fail $ "Inferred type doesn't match expected type:\n"
                                            ++ "Inferred: " ++ show (typeOf e')
                                            ++ "\nExpected: " ++ show t
typeExpr (U.Const c@(Int _)) =  pure $ Ty.Const intT c
typeExpr (U.Const c@(Bool _)) = pure $ Ty.Const boolT c
typeExpr (U.Var v i) = do
                        t <- instantiate =<< lookupVariable v
                        pure $ Ty.Var t v i
typeExpr (U.Let n e1 e2) = do
                            e1' <- typeExpr e1
                            e2' <- addToEnv n (generalise $ typeOf e1') (typeExpr e2) 
                            let t = typeOf e2'
                            pure $ Ty.Let t n e1' e2'
typeExpr (U.If e1 e2 e3) = do
                            e1' <- typeExpr e1
                            unify (typeOf e1') boolT
                            e2' <- typeExpr e2
                            e3' <- typeExpr e3
                            unify (typeOf e2') (typeOf e3')
                            applyS $ pure (Ty.If (typeOf e2') e1' e2' e3')
typeExpr (U.App e1 args) = do
                                v <- freshTyVar
                                e1' <- typeExpr e1
                                args' <- mapM typeExpr args
                                unify (typeOf e1') (foldr Fn (Var v) (map typeOf args'))
                                applyS $ pure $ Ty.App (Var v) e1' args'
typeExpr (U.BinOp op@(Op o _) e1 e2) = do
                                
                                e1' <- typeExpr e1
                                e2' <- typeExpr e2
                                v <- freshTyVar
                                to <- instantiate =<< lookupVariable o
                                unify to (Fn (typeOf e1') (Fn (typeOf e2') (Var v)))
                                applyS $ pure $ Ty.BinOp (Var v) op e1' e2'
typeExpr U.Nil = do
                    v <- freshTyVar
                    pure $ Ty.Nil (Var v)
typeExpr (U.Iter n e1 e2) = do
                             e1' <- typeExpr e1
                             fv1 <- freshTyVar
                             let v1 = Var fv1
                             unify (TyC "List" [v1]) $ typeOf e1'
                             t <- applyS (return v1)
                             e2' <- addToEnv n (Ty t) (typeExpr e2)
                             let t' = typeOf e2'
                             applyS $ pure $ Ty.Iter (listT t') n e1' e2'
typeExpr (U.IterG n e1 e2 e3) = do
                                 e1' <- typeExpr e1
                                 fv1 <- freshTyVar
                                 let v1 = Var fv1
                                 unify (TyC "List" [v1]) $ typeOf e1'
                                 t <- applyS $ pure v1
                                 e2' <- addToEnv n (Ty t) (typeExpr e2)
                                 unify (typeOf e2') boolT
                                 e3' <- addToEnv n (Ty t) (typeExpr e3)
                                 let t' = typeOf e2'
                                 applyS $ pure $ Ty.IterG (listT t') n e1' e2' e3'
typeExpr (U.Proj l e i) = do
                            e' <- typeExpr e
                            fv <- freshTyVar
                            let v = liftTypeN l (Var fv)
                            unify (typeOf e') v
                            t <- applyS $ pure $ Var fv
                            case t of
                                (TyC "tuple" ts) -> if length ts < i
                                                        then error $ "Projection expected a tuple type with at least " ++ show i ++ " elements"
                                                        else pure $ Ty.Proj (liftTypeN l $ ts !! (i - 1)) l e' i
                                _                -> error $ "Projection expects a tuple or (nested-)list of tuples as first argument but was given: " ++ show (typeOf e')
typeExpr (e@(U.Fn _ _ _ _ _)) = typeFunction e

instantiate :: TypeScheme -> AlgW Type
instantiate (Forall n t) = do
                            v <- freshTyVar
                            localAddSubstitution n (Var v) $ instantiate t
instantiate (Ty t) = applyS $ pure t

instance Substitutable  ([Ty.Expr], Ty.Expr) where
    apply s (es, e) = (map (apply s) es, apply s e)

instance Substitutable Ty.Expr where
    apply s (Ty.App t e1 es) = Ty.App (apply s t) (apply s e1) (map (apply s) es)
    apply s (Ty.Fn t n i args e) = Ty.Fn (apply s t) n i args (apply s e)
    apply s (Ty.Let t n e1 e2) = Ty.Let (apply s t) n (apply s e1) (apply s e2)
    apply s (Ty.If t e1 e2 e3) = Ty.If (apply s t) (apply s e1) (apply s e2) (apply s e3)
    apply s (Ty.BinOp t o e1 e2) = Ty.BinOp (apply s t) o (apply s e1) (apply s e2)
    apply s (Ty.Const t v) = Ty.Const (apply s t) v
    apply s (Ty.Var t x i) = Ty.Var (apply s t) x i
    apply s (Ty.Iter t x e1 e2) = Ty.Iter (apply s t) x (apply s e1) (apply s e2)
    apply s (Ty.IterG t x e1 e2 e3) = Ty.IterG (apply s t) x (apply s e1) (apply s e2) (apply s e3)
    apply s (Ty.Nil t) = Ty.Nil (apply s t)
    apply s (Ty.Proj t l e i) = Ty.Proj (apply s t) l (apply s e) i