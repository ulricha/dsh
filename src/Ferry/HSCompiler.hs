{-# LANGUAGE MultiParamTypeClasses, ScopedTypeVariables #-}
module Ferry.HSCompiler (fromQ) where

import Ferry.Data
import Ferry.Syntax as F
import Ferry.Compiler
import Ferry.Impossible
import Ferry.Compile as C

import Data.Char
-- import Data.Convertible
import Database.HDBC

import Control.Monad.State
import Control.Applicative

import Data.List (nub)
import qualified Data.List as L

import Data.Generics (listify)
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

-- * Convert DB queries into Haskell values
fromQ :: (QA a, IConnection conn) => conn -> Q a -> IO a
fromQ c a = evaluate c a >>= (return . fromNorm)

evaluate :: forall a. forall conn. (QA a, IConnection conn)
         => conn                -- ^ The HDBC connection
         -> Q a
         -> IO Norm
evaluate c q@(Q e) = do
                let algPlan = ((C.Algebra (doCompile q))::AlgebraXML a)
                tables <- mapM (getTableInfo c) $ getTableNames e
                executePlan c algPlan
                   
doCompile :: Q a -> String
doCompile (Q a) = typedCoreToAlgebra $ runN $ transformE a

transformE :: Exp -> N CoreExpr
transformE (UnitE ::: _) = return undefined
transformE ((BoolE b) ::: _) = return $ Constant ([] :=> bool) $ CBool b
transformE ((CharE c) ::: _) = return $ Constant ([] :=> string) $ CString [c] 
transformE ((IntegerE i) ::: _) = return $ Constant ([] :=> int) $ CInt i
transformE ((DoubleE d) ::: _) = return $ Constant ([] :=> float) $ CFloat d
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
transformE ((TableE n) ::: ty) = do
                                    fv <- freshVar
                                    let tTy@(FList (FRec ts)) = flatFTy ty
                                    let varB = Var ([] :=> FRec ts) $ prefixVar fv
                                    let cols = [Column ('a':i) t | (RLabel i, t) <- ts]
                                    let keys = [Key $ map (\(Column n' _) -> n') cols]
                                    let table' = Table ([] :=> tTy) n cols keys
                                    let pattern = PVar $ prefixVar fv
                                    -- pattern = (\(Key s) -> Pattern s) $ head keys
                                    let nameType = map (\((Column name t), nr) -> (nr, t)) $ zip cols [1..]
                                    let body = foldr (\(nr, t) b -> 
                                                    let (_ :=> bt) = typeOf b
                                                     in Rec ([] :=> FRec [(RLabel "1", t), (RLabel "2", bt)]) [RecElem ([] :=> t) "1" (F.Elem ([] :=> t) varB (show nr)), RecElem ([] :=> bt) "2" b])
                                                  ((\(nr,t) -> F.Elem ([] :=> t) varB (show nr)) $ last nameType)
                                                  (init nameType)
                                    let ([] :=> rt) = typeOf body
                                    let lambda = ParAbstr ([] :=> FRec ts .-> rt) pattern body
                                    return $ App ([] :=> FList rt) (App ([] :=> (FList $ FRec ts) .-> FList rt) 
                                                                    (Var ([] :=> (FRec ts .-> rt) .-> (FList $ FRec ts) .-> FList rt) "map") 
                                                                    lambda)
                                                                   (ParExpr (typeOf table') table')
transformE _ = $impossible       

transformArg :: Exp -> N Param                                 
transformArg ((LamE f) ::: ty) = do
                                  n <- freshVar
                                  let (ArrowT t1 _) = ty
                                  let fty = transformTy ty
                                  let e1 = f $ (VarE n) ::: t1
                                  ParAbstr ([] :=> fty) (PVar $ prefixVar n) <$> transformE e1
transformArg e@(_ ::: _) = (\e' -> ParExpr (typeOf e') e') <$> transformE e 
transformArg _ = $impossible
                                  
parExpr :: CoreExpr -> Param
parExpr c = ParExpr (typeOf c) c

flatFTy :: Type -> FType
flatFTy = FList . FRec . flatFTy' 1
 where
     flatFTy' :: Int -> Type -> [(RLabel, FType)]
     flatFTy' i (TupleT t1 t2) = (RLabel $ show i, transformTy t1) : (flatFTy' (i + 1) t2)
     flatFTy' i t              = [(RLabel $ show i, transformTy t)]

sizeOfTy :: Type -> Int
sizeOfTy (TupleT _ t2) = 1 + sizeOfTy t2
sizeOfTy _              = 1 

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

getTableNames :: Exp -> [String]
getTableNames e = nub $ map (\(TableE n) -> n) $ listify isTable e
    where 
        isTable :: Exp -> Bool
        isTable (TableE _) = True
        isTable _         = False
        
getTableInfo :: IConnection conn => conn -> String -> IO (String, [(String, (Type -> Bool))])
getTableInfo c n = do
                    info <- describeTable c n
                    return $ (n, toTableDescr info)
                    
        where
          toTableDescr :: [(String, SqlColDesc)] -> [(String, (Type -> Bool))]
          toTableDescr = map (\(n, props) -> (n, compatibleType (colType props)))
          compatibleType :: SqlTypeId -> Type -> Bool
          compatibleType dbT hsT = case hsT of
                                        UnitT -> True
                                        BoolT -> L.elem dbT [SqlSmallIntT, SqlIntegerT, SqlBitT]
                                        CharT -> L.elem dbT [SqlCharT, SqlWCharT]
                                        IntegerT -> L.elem dbT [SqlSmallIntT, SqlIntegerT, SqlTinyIntT, SqlBigIntT, SqlNumericT]
                                        DoubleT -> L.elem dbT [SqlDecimalT, SqlRealT, SqlFloatT, SqlDoubleT]
                                        _       -> error $ "You can't store this kind of data in a table..."

                    
