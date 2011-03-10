module Language.ParallelLang.NKL.TypeInferencer.Unification (unify) where
    
import Language.ParallelLang.NKL.TypeInferencer.Types
import Language.ParallelLang.Common.Data.Type

import Control.Applicative

unify :: Type -> Type -> AlgW ()
unify a  b = do
                a' <- applyS $ pure a
                b' <- applyS $ pure b
                unify' a' b'

unify' :: Type -> Type -> AlgW ()
unify' (Var v1) t2 = updateSubstitution v1 t2
unify' t1 (Var v2) = updateSubstitution v2 t1
unify' t1@(TyC n1 args1) t2@(TyC n2 args2) = case n1 == n2 of
                                        True -> unifyL args1 args2
                                        False -> error $ "Type constructors do not match:\n" ++ show t1 ++ " cannot be unified with: " ++ show t2
unify' (Fn t11 t12) (Fn t21 t22) = do
                                    unify t11 t21
                                    unify t12 t22
unify' _ _ = error "Types do not match"
                                        
unifyL :: [Type] -> [Type] -> AlgW () 
unifyL (x:xs) (y:ys) = do 
                         unify x y 
                         unifyL xs ys
unifyL [] [] = return ()
unifyL _ _ = error "Types have different number of arguments"