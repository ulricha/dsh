{-# LANGUAGE TemplateHaskell, RelaxedPolyRec, FlexibleInstances, UndecidableInstances  #-}
module Database.DSH.CompileFlattening (toNKL) where

import Database.DSH.Impossible

import qualified Language.ParallelLang.NKL.Data.NKL as NKL
import qualified Language.ParallelLang.Common.Data.Val as V
import qualified Language.ParallelLang.Common.Data.Type as T
import qualified Language.ParallelLang.Common.Data.Op as O

import Database.DSH.Data as D
import Data.Text (unpack)

import qualified Data.Map as M

import Control.Monad
import Control.Monad.State
import Control.Applicative
  
import GHC.Exts(sortWith)

import Data.Char (toLower)
{-
N monad, version of the state monad that can provide fresh variable names.
-}
type N = StateT (Int, M.Map String [(String, (T.Type -> Bool))], String -> IO [(String, T.Type -> Bool)]) IO

{-
class DBConn conn where
    getTableInfo :: conn -> String -> IO [(String, (T.Type -> Bool))]

instance IConnection conn => DBConn conn where
    -- | Retrieve through the given database connection information on the table (columns with their types)
    -- which name is given as the second argument.        
    -- getTableInfo :: IConnection conn => conn -> String -> IO [(String, (T.Type -> Bool))]
    getTableInfo c n = do
                     info <- describeTable c n
                     return $ toTableDescr info

         where
           toTableDescr :: [(String, SqlColDesc)] -> [(String, (T.Type -> Bool))]
           toTableDescr = L.sortBy (\(n1, _) (n2, _) -> compare n1 n2) . map (\(name, props) -> (name, compatibleType (colType props)))
           compatibleType :: SqlTypeId -> T.Type -> Bool
           compatibleType dbT hsT = case hsT of
                                         T.Unit -> True
                                         T.Bool -> L.elem dbT [SqlSmallIntT, SqlIntegerT, SqlBitT]
                                         T.String -> L.elem dbT [SqlCharT, SqlWCharT, SqlVarCharT]
                                         T.Int -> L.elem dbT [SqlSmallIntT, SqlIntegerT, SqlTinyIntT, SqlBigIntT, SqlNumericT]
                                         T.Double -> L.elem dbT [SqlDecimalT, SqlRealT, SqlFloatT, SqlDoubleT]
                                         t       -> error $ "You can't store this kind of data in a table... " ++ show t ++ " " ++ show n
-}

-- | Lookup information that describes a table. If the information is 
-- not present in the state then the connection is used to retrieve the
-- table information from the Database.
tableInfo :: String -> N [(String, (T.Type -> Bool))]
tableInfo t = do
               (i, env, f) <- get
               case M.lookup t env of
                     Nothing -> do
                                 inf <- getTableInfoFun t
                                 put (i, M.insert t inf env, f)
                                 return inf                                      
                     Just v -> return v

-- | Provide a fresh identifier name during compilation
freshVar :: N Int
freshVar = do
             (i, m, f) <- get
             put (i + 1, m, f)
             return i

prefixVar :: Int -> String
prefixVar i = "*dshVar*" ++ show i


getTableInfoFun :: String -> N [(String, T.Type -> Bool)]
getTableInfoFun n = do
                   (_, _, f) <- get
                   lift $ f n

toNKL :: (String -> IO [(String, T.Type -> Bool)]) -> Exp -> IO NKL.Expr
toNKL f e = runN f $ translate e

-- | Execute the transformation computation. During
-- compilation table information can be retrieved from
-- the database, therefor the result is wrapped in the IO
-- Monad.      
runN :: (String -> IO [(String, T.Type -> Bool)]) -> N a -> IO a
runN f = liftM fst . flip runStateT (1, M.empty, f)


translate ::  Exp -> N NKL.Expr
translate (UnitE _) = return $ NKL.Const T.unitT V.Unit
translate (BoolE b _) = return $ NKL.Const T.boolT $ V.Bool b
translate (CharE c _) = return $ NKL.Const T.stringT $ V.String [c]
translate (IntegerE i _) = return $ NKL.Const T.intT $ V.Int (fromInteger i)
translate (DoubleE d _) = return $ NKL.Const T.doubleT $ V.Double d 
translate (TextE t _) = return $ NKL.Const T.stringT $ V.String (unpack t) 
translate (VarE i ty) = return $ NKL.Var (ty2ty ty) (prefixVar i)
translate (TableE (TableDB n ks) ty) = do
                                        let ts = zip [1..] $ tableTypes ty
                                        tableDescr <- liftM (sortWith fst) $ tableInfo n
                                        let tyDescr = if length tableDescr == length ts
                                                        then zip tableDescr ts
                                                        else error $ "Inferred typed: " ++ show ts ++ " \n doesn't match type of table: \"" 
                                                                ++ n ++ "\" in the database. The table has the shape: " ++ (show $ map fst tableDescr) ++ ". " ++ show ty
                                        let cols = [(cn, t) | ((cn, f), (i, t)) <- tyDescr, legalType n cn i t f]
                                        let ks' = if ks == []
                                                    then [map fst tableDescr]
                                                    else ks
                                        return $ NKL.Table (ty2ty ty) n cols ks'
translate (TupleE e1 e2 _) = do
                                c1 <- translate e1
                                c2 <- translate e2
                                let t1 = T.typeOf c1
                                let t2 = T.typeOf c2
                                let t = (T.pairT t1 t2) 
                                case (c1, c2) of
                                    (NKL.Const _ v1, NKL.Const _ v2) -> return $ NKL.Const t (V.Pair v1 v2)
                                    _                                -> return $ NKL.Pair t c1 c2
translate (ListE es ty) = toList (NKL.Const (ty2ty ty) (V.List [])) <$> mapM translate es
translate (LamE f ty) = do
                        v <- freshVar
                        let (ArrowT t1 _) = ty
                        f' <- translate $ f (VarE v t1)
                        return $ NKL.Lam (ty2ty ty) (prefixVar v) f' 
translate (AppE1 Fst e1 _) = do
                                c1 <- translate e1
                                let t1 = T.typeOf c1
                                return $ NKL.Fst (fst $ T.pairComponents t1) c1
translate (AppE1 Snd e1 _) = do
                                c1 <- translate e1
                                let t1 = T.typeOf c1
                                return $ NKL.Snd (snd $ T.pairComponents t1) c1
translate (AppE1 f e1 ty) = do 
                                c1 <- translate e1
                                return $ NKL.App (ty2ty ty) (NKL.Var (T.typeOf c1 T..-> ty2ty ty) (map toLower $ show f)) c1
translate (AppE2 Map e1 e2 ty) = do
                                  c1 <- translate e1
                                  c2 <- translate e2
                                  return $ NKL.App (ty2ty ty) (NKL.App (ty2ty $ ArrowT (typeExp e2) ty) (NKL.Var (ty2ty $ ArrowT (typeExp e1) (ArrowT (typeExp e2) ty)) "map") c1) c2
translate (AppE2 GroupWith f e ty) = do
                                      c1 <- translate f
                                      c2 <- translate e
                                      return $ NKL.App (ty2ty ty) (NKL.App (ty2ty $ ArrowT (typeExp e) ty) (NKL.Var (ty2ty $  ArrowT (typeExp f) (ArrowT (typeExp e) ty)) "groupWith") c1) c2
translate (AppE2 SortWith f e ty) = do
                                        c1 <- translate f
                                        c2 <- translate e
                                        return $ NKL.App (ty2ty ty) (NKL.App (ty2ty $ ArrowT (typeExp e) ty) (NKL.Var (ty2ty $  ArrowT (typeExp f) (ArrowT (typeExp e) ty)) "sortWith") c1) c2
translate (AppE2 D.Cons e1 e2 _) = do
                                            e1' <- translate e1
                                            e2' <- translate e2
                                            return $ toList e2' [e1']  
translate (AppE2 f2 e1 e2 ty) = do
                                        let tr = ty2ty ty
                                        e1' <- translate e1
                                        e2' <- translate e2
                                        return $ NKL.BinOp tr (transformOp f2) e1' e2'
translate (AppE3 Cond e1 e2 e3 _) = do
                                             e1' <- translate e1
                                             e2' <- translate e2
                                             e3' <- translate e3
                                             return $ NKL.If (T.typeOf e2') e1' e2' e3'
translate (TableE (TableCSV _) _) = $impossible
translate (AppE3 ZipWith _ _ _ _) = $impossible

legalType :: String -> String -> Int -> T.Type -> (T.Type -> Bool) -> Bool
legalType tn cn nr t f = case f t of
                            True -> True
                            False -> error $ "The type: " ++ show t ++ "\nis not compatible with the type of column nr: " ++ show nr
                                                ++ " namely: " ++ cn ++ "\n in table " ++ tn ++ "."

gtorlt :: Fun2 -> Fun2
gtorlt Gte = Gt
gtorlt Lte = Lt
gtorlt _   = $impossible

cons :: NKL.Expr -> NKL.Expr -> NKL.Expr
cons e1 e2 = NKL.BinOp (NKL.typeOf e2) (O.Op O.Cons False) e1 e2

isTuple :: String -> Maybe Int
isTuple ('(':xs) = let l = length xs
                       s = (replicate (l - 1) ',' ) ++ ")"
                    in if (xs == s) then Just (l - 1) else Nothing
isTuple _      = Nothing

ty2ty :: Type -> T.Type
ty2ty UnitT = T.unitT
ty2ty BoolT = T.boolT
ty2ty CharT = T.stringT 
ty2ty IntegerT = T.intT
ty2ty DoubleT = T.doubleT
ty2ty TextT = T.stringT
ty2ty (TupleT t1 t2) = T.pairT (ty2ty t1) (ty2ty t2)
ty2ty (ListT t) = T.listT (ty2ty t)
ty2ty (ArrowT t1 t2) = (ty2ty t1) T..-> (ty2ty t2)

tableTypes :: Type -> [T.Type]
tableTypes (ListT t) = fromTuples t
    where
        fromTuples :: Type -> [T.Type]
        fromTuples (TupleT t1 t2) = ty2ty t1 : fromTuples t2
        fromTuples t'              = [ty2ty t']
tableTypes _         = $impossible

-- | Translate the DSH operator to Ferry Core operators
transformOp :: Fun2 -> O.Op
transformOp Add = O.Op O.Add False
transformOp Sub = O.Op O.Sub False
transformOp Mul = O.Op O.Mul False
transformOp Div = O.Op O.Div False
transformOp Equ = O.Op O.Eq False
transformOp Lt = O.Op O.Lt False
transformOp Lte = O.Op O.LtE False
transformOp Gte = O.Op O.GtE False
transformOp Gt = O.Op O.Gt False
transformOp Conj = O.Op O.Conj False
transformOp Disj = O.Op O.Disj False
transformOp _ = $impossible 

toList :: NKL.Expr -> [NKL.Expr] -> NKL.Expr
toList n es = primList (reverse es) n 
    where
        primList :: [NKL.Expr] -> NKL.Expr -> NKL.Expr
        primList ((NKL.Const _ v):vs) (NKL.Const ty (V.List xs)) = primList vs (NKL.Const ty (V.List (v:xs)))
        primList [] e = e
        primList vs (NKL.Const ty (V.List [])) = consList vs (NKL.Nil ty)
        primList vs e = consList vs e
        consList :: [NKL.Expr] -> NKL.Expr -> NKL.Expr
        consList xs e = foldl (flip cons) e xs
        
isConst :: NKL.Expr -> Bool
isConst (NKL.Const _ _) = True
isConst _               = False

isPrimVal :: Exp -> Bool
isPrimVal (UnitE _) = True
isPrimVal (BoolE _ _) = True
isPrimVal (CharE _ _) = True
isPrimVal (IntegerE _ _) = True
isPrimVal (ListE es _) = and $ map isPrimVal es
isPrimVal (DoubleE _ _) = True
isPrimVal (TextE _ _) = True
isPrimVal (TupleE e1 e2 _) = isPrimVal e1 && isPrimVal e2
isPrimVal _ = False
