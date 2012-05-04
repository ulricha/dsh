{-# LANGUAGE TemplateHaskell #-}
module Database.DSH.DeriveConstructors where

import qualified Database.DSH.Data as D
import qualified Database.DSH.Combinators as C
import Language.Haskell.TH
-- import Language.Haskell.TH.Lib
import Data.Char
import Control.Monad
    
typeInfo :: Name -> Q [Dec]
typeInfo v = do
                c <- reify v
                runIO $ putStrLn $ show c
                return []
                
deriveQAConstructors :: Name -> Q [Dec]
deriveQAConstructors n = do
                          (TyConI (DataD ctxt name vars constructors names)) <- reify n
                          let constructors' = map constructorInformation constructors
                          let allTypes = map (\(_,x,_) -> x) constructors' 
                          liftM concat $ mapM (mkConstructor (length constructors) ctxt name vars allTypes) $ zip [1..] constructors' 


constructorInformation :: Con -> (Name, Type, [Type])
constructorInformation (NormalC n tys) = let constructorName = mkName $ (\(x:xs) -> toLower x : xs) $ nameBase n
                                             argTy = map snd tys
                                             rt = if length argTy > 0
                                                    then foldr1 pairT argTy
                                                    else TupleT 0
                                          in (constructorName, rt, argTy)
constructorInformation (RecC n tys) = constructorInformation (NormalC n $ map (\(_, l,t) -> (l, t)) tys)

wrapQ :: Type -> Type
wrapQ t = AppT (ConT ''D.Q) t

arrow :: Type -> Type -> Type
arrow t1 t2 = AppT (AppT ArrowT t1) t2

pairT :: Type -> Type -> Type
pairT t1 t2 = AppT (AppT (TupleT 2) t1) t2

mkConstraint :: Type -> Pred
mkConstraint t = ClassP ''D.QA [t]

mkConstructor :: Int -> Cxt -> Name -> [TyVarBndr] -> [Type] -> (Int, (Name, Type, [Type])) -> Q [Dec]
mkConstructor nrConstructors ctxt typeName vs rtys (i, (cName, _, argTys)) = do
                                                let constructorName = mkName $ (\(x:xs) -> toLower x : xs) $ nameBase cName
                                                let tau = foldl AppT (ConT typeName) $ map tyVarBndr2tyVar vs
                                                let ctxt' = map (mkConstraint . tyVarBndr2tyVar) vs ++ ctxt
                                                let rt = wrapQ tau
                                                return [mkTypeSig rt constructorName ctxt' vs argTys, mkConstructorBody nrConstructors constructorName rtys (i, length argTys)]

mkTypeSig :: Type -> Name -> Cxt -> [TyVarBndr] -> [Type] -> Dec
mkTypeSig rt constrName cxt vars args = SigD constrName $ if length vars > 0
                                                       then ForallT vars cxt $ foldr arrow rt (map wrapQ args)
                                                       else foldr arrow rt (map wrapQ args)

mkConstructorBody :: Int -> Name -> [Type] -> (Int, Int) -> Dec
mkConstructorBody t tn rtys (i, argN) = FunD tn [Clause [VarP n | n <- varNames] (NormalB $ newQ elements) []]
       where
           elements :: Exp
           elements = foldr1 pair [if n == i then element else typedNil rt | (n, rt) <- zip [1..t] rtys]
           element :: Exp
           element = AppE (VarE 'C.singleton) $ if length vars > 0
                                                 then foldr1 pair vars
                                                 else VarE 'C.unit
           vars :: [Exp]
           vars = map VarE varNames
           varNames :: [Name]
           varNames = [mkName $ "var_" ++ show i | i <- [1..argN]]

pair :: Exp -> Exp -> Exp
pair e1 e2 = AppE (AppE (VarE 'C.pair) e1 ) e2

newQ :: Exp -> Exp
newQ e1 = AppE (ConE 'D.Q) (AppE (VarE 'D.forget) e1)

typedNil :: Type -> Exp
typedNil t = SigE (VarE 'C.nil) (wrapQ $ AppT ListT t)

tyVarBndr2tyVar :: TyVarBndr -> Type
tyVarBndr2tyVar (PlainTV n) = VarT n
tyVarBndr2tyVar (KindedTV n _) = VarT n