{-# LANGUAGE MultiParamTypeClasses, ScopedTypeVariables #-}
module Ferry.HSCompiler (fromQ) where

import Ferry.Data
import Ferry.Syntax as F
import Ferry.Compiler
import Ferry.Impossible
import Ferry.Compile as C

import Ferry.Syntax (FType (..))

import Data.Maybe (fromJust)
import Data.Char
-- import Data.Convertible
import Database.HDBC

import Control.Monad.State
import Control.Monad.Reader
import Control.Applicative

import Data.List (nub)
import qualified Data.List as L

import Data.Generics (listify)

import System.IO.Unsafe

{-
N monad, version of the state monad that can provide fresh variable names.
-}
newtype N a = N (ReaderT [(String, [(String, (FType -> Bool))])] (State Int) a)

unwrapN :: N a -> ReaderT [(String, [(String, (FType -> Bool))])] (State Int) a
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

tableInfo :: String -> N [(String, (FType -> Bool))]
tableInfo t = N $ do
                    env <- ask
                    return $ fromJust $ lookup t env
                
prefixVar :: Int -> String
prefixVar = ((++) "__fv_") . show
     
runN :: [(String, [(String, (FType -> Bool))])] -> N a -> a
runN env = fst . flip runState 1 . flip runReaderT env . unwrapN
            
-- * Convert DB queries into Haskell values
fromQ :: (QA a, IConnection conn) => conn -> Q a -> IO a
fromQ c a = evaluate c a >>= (return . fromNorm)

evaluate :: forall a. forall conn. (QA a, IConnection conn)
         => conn                -- ^ The HDBC connection
         -> Q a
         -> IO Norm
evaluate c q@(Q e) = do
                tables <- mapM (getTableInfo c) $ getTableNames e
                let algPlan = ((C.Algebra (doCompile tables q))::AlgebraXML a)
                executePlan c algPlan
                   
doCompile :: [(String, [(String, (FType -> Bool))])] -> Q a -> String
doCompile env (Q a) = typedCoreToAlgebra $ runN env $ transformE a

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
                                        case elem f2 [Add, Mul, Equ, Lt, Lte, Gte, Gt] of
                                            True  -> do
                                                      e1' <- transformE e1
                                                      e2' <- transformE e2
                                                      return $ BinOp ([] :=> tr) (transformOp f2) e1' e2'
                                            False -> do
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
                                    tableDescr <- tableInfo n
                                    let tyDescr = case length tableDescr == length ts of
                                                    True -> zip tableDescr ts
                                                    False -> error $ "Inferred typed: " ++ show tTy ++ " \n doesn't match type of table: \"" 
                                                                        ++ n ++ "\" in the database. The table has the shape: " ++ (show $ map fst tableDescr) ++ ". " ++ show ty 
                                    let cols = [Column cn t | ((cn, f), (RLabel i, t)) <- tyDescr, legalType n cn i t f]
                                    let keys = [Key $ map (\(Column n' _) -> n') cols]
                                    let table' = Table ([] :=> tTy) n cols keys
                                    {- let pattern = PVar $ prefixVar fv
                                    let nameType = map (\((Column name t), nr) -> (nr, t)) $ zip cols [1..]
                                    let body = foldr (\(nr, t) b -> 
                                                    let (_ :=> bt) = typeOf b
                                                     in Rec ([] :=> FRec [(RLabel "1", t), (RLabel "2", bt)]) [RecElem ([] :=> t) "1" (F.Elem ([] :=> t) varB (show nr)), RecElem ([] :=> bt) "2" b])
                                                  ((\(nr,t) -> F.Elem ([] :=> t) varB (show nr)) $ last nameType)
                                                  (init nameType)
                                    let ([] :=> rt) = typeOf body
                                    let lambda = ParAbstr ([] :=> FRec ts .-> rt) pattern body
                                    let expr = App ([] :=> FList rt) (App ([] :=> (FList $ FRec ts) .-> FList rt) 
                                                                    (Var ([] :=> (FRec ts .-> rt) .-> (FList $ FRec ts) .-> FList rt) "map") 
                                                                    lambda)
                                                                   (ParExpr (typeOf table') table') -}
                                    return table'
    where
        legalType :: String -> String -> String -> FType -> (FType -> Bool) -> Bool
        legalType tn cn nr ty f = case f ty of
                                True -> True
                                False -> error $ "The type: " ++ show ty ++ "\nis not compatible with the type of column nr: " ++ nr
                                                    ++ " namely: " ++ cn ++ "\n in table " ++ tn ++ "."
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
flatFTy (ListT t) = FList $ FRec $ flatFTy' 1 t
 where
     flatFTy' :: Int -> Type -> [(RLabel, FType)]
     flatFTy' i (TupleT t1 t2) = (RLabel $ show i, transformTy t1) : (flatFTy' (i + 1) t2)
     flatFTy' i t              = [(RLabel $ show i, transformTy t)]
flatFTy _         = $impossible

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

transformOp :: Fun2 -> Op
transformOp Add = Op "+"
transformOp Mul = Op "*"
transformOp Equ = Op "=="
transformOp Lt = Op "<"
transformOp Lte = Op "<="
transformOp Gte = Op ">="
transformOp Gt = Op ">"
transformOp _ = $impossible

transformF :: (Show f) => f -> FType -> CoreExpr
transformF f t = Var ([] :=> t) $ (\(x:xs) -> toLower x : xs) $ show f

getTableNames :: Exp -> [String]
getTableNames e = nub $ map (\(TableE n) -> n) $ listify isTable e
    where 
        isTable :: Exp -> Bool
        isTable (TableE _) = True
        isTable _         = False
        
getTableInfo :: IConnection conn => conn -> String -> IO (String, [(String, (FType -> Bool))])
getTableInfo c n = do
                    info <- describeTable c n
                    return $ (n, toTableDescr info)
                    
        where
          toTableDescr :: [(String, SqlColDesc)] -> [(String, (FType -> Bool))]
          toTableDescr = L.sortBy (\(n1, _) (n2, _) -> compare n1 n2) . map (\(n, props) -> (n, compatibleType (colType props)))
          compatibleType :: SqlTypeId -> FType -> Bool
          compatibleType dbT hsT = case hsT of
                                        FUnit -> True
                                        FBool -> L.elem dbT [SqlSmallIntT, SqlIntegerT, SqlBitT]
                                        FString -> L.elem dbT [SqlCharT, SqlWCharT]
                                        FInt -> L.elem dbT [SqlSmallIntT, SqlIntegerT, SqlTinyIntT, SqlBigIntT, SqlNumericT]
                                        FFloat -> L.elem dbT [SqlDecimalT, SqlRealT, SqlFloatT, SqlDoubleT]
                                        _       -> error $ "You can't store this kind of data in a table..."
{-
ast = 
  App (App (Var "map") (\__fv_1 -> {__fv_1."1", __fv_1."2" })) (Table "someints") -}
-- map (\x -> (x.columna2, x.columnb1)) (table someints (columna2 Int, columnb1 Float) with keys ((columna2)))