{-# LANGUAGE MultiParamTypeClasses #-}
module Ferry.Compiler (evaluate) where

import Ferry.Data
import Ferry.Syntax as F
import Ferry.Compiler.Transform
import Ferry.Impossible

import Data.Char
-- import Data.Convertible
import Database.HDBC

import Control.Monad.State
import Control.Applicative
{-
N monad, version of the state monad that can provide fresh variable names.
-}
newtype N a = N (State Int a)

unwrapN :: N a -> State Int a
unwrapN (N s) = s

instance Functor N where
    fmap f a = N $ fmap f $ unwrapN a

instance Monad N where
    s >>= m = N (unwrapN s >>= unwrapN . m)
    return = N . return
    
instance Applicative N where
  pure  = return
  (<*>) = ap

freshVar :: N Int
freshVar = N $ do
                i <- get
                put (i + 1)
                return i
                
prefixVar :: Int -> String
prefixVar = ((++) "__fv_") . show
     
runN :: N a -> a
runN = fst . (flip runState 1) . unwrapN

evaluate :: IConnection conn
         => conn                -- ^ The HDBC connection
         -> Exp
         -> IO Norm
evaluate = undefined

transformE :: Exp -> N CoreExpr
transformE UnitE = return undefined
transformE (BoolE b) = return $ Constant ([] :=> bool) $ CBool b
transformE (CharE c) = return $ Constant ([] :=> string) $ CString [c] 
transformE (IntegerE i) = return $ Constant ([] :=> int) $ CInt i
transformE (DoubleE d) = return $ Constant ([] :=> float) $ CFloat d
transformE ((TupleE e1 e2) ::: ty) = do
                                        c1 <- transformE e1
                                        c2 <- transformE e2
                                        return $ Rec ([] :=> transformTy ty) [RecElem (typeOf c1) "1" c1, RecElem (typeOf c2) "2" c2] 
transformE ((ListE es) ::: ty) = let qt = ([] :=> transformTy ty) 
                                  in foldr (\h t -> F.Cons qt h t) (Nil qt) <$> mapM transformE es
transformE ((AppE f a) ::: ty) = transformE $ f a ::: ty
transformE ((AppE1 f1 e1) ::: ty) = do
                                      let tr = transformTy ty
                                      e1' <- transformArg e1
                                      let (_ :=> ta) = typeOf e1'
                                      return $ App ([] :=> tr) (transformF f1 (ta .-> tr)) e1'
transformE ((AppE2 f2 e1 e2) ::: ty) = do
                                        let tr = transformTy ty
                                        e1' <- transformArg e1
                                        e2' <- transformArg e2
                                        let (_ :=> ta1) = typeOf e1'
                                        let (_ :=> ta2) = typeOf e2'
                                        return $ App ([] :=> tr) 
                                                    (App ([] :=> ta2 .-> tr) (transformF f2 (ta1 .-> ta2 .-> tr)) e1')
                                                    e2'
transformE ((AppE3 f3 e1 e2 e3) ::: ty) = do
                                           let tr = transformTy ty
                                           e1' <- transformArg e1
                                           e2' <- transformArg e2
                                           e3' <- transformArg e3
                                           let (_ :=> ta1) = typeOf e1'
                                           let (_ :=> ta2) = typeOf e2'
                                           let (_ :=> ta3) = typeOf e3'
                                           return $ App ([] :=> tr)
                                                        (App ([] :=> ta3 .-> tr)
                                                             (App ([] :=> ta2 .-> ta3 .-> tr) (transformF f3 (ta1 .-> ta2 .-> ta3 .-> tr)) e1')
                                                             e2')
                                                        e3'
transformE ((VarE i) ::: ty) = return $ Var ([] :=> transformTy ty) $ prefixVar i
                                 

transformArg :: Exp -> N Param                                 
transformArg ((LamE f) ::: ty) = do
                                  n <- freshVar
                                  let (ArrowT t1 t2) = ty
                                  let fty = transformTy ty
                                  let e1 = f $ (VarE n) ::: t1
                                  ParAbstr ([] :=> fty) (PVar $ prefixVar n) <$> transformE e1
transformArg e@(_ ::: _) = (\e -> ParExpr (typeOf e) e) <$> transformE e 
transformArg _ = $impossible
                                  
parExpr :: CoreExpr -> Param
parExpr c = ParExpr (typeOf c) c
{-
data Exp =
  | TableE String
  | VarE Int
  | Exp ::: Type
-}
transformTy :: Type -> FType
transformTy UnitT = undefined
transformTy BoolT = bool
transformTy CharT = string
transformTy IntegerT = int
transformTy DoubleT = float
transformTy (TupleT t1 t2) = FRec [(RLabel "1", transformTy t1), (RLabel "2", transformTy t2)]
transformTy (ListT t1) = FList $ transformTy t1
transformTy (ArrowT t1 t2) = (transformTy t1) .-> (transformTy t2)

transformF :: (Show f) => f -> FType -> CoreExpr
transformF f t = Var ([] :=> t) $ (\(x:xs) -> toLower x : xs) $ show f


