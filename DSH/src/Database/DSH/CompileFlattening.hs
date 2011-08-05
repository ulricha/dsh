{-# LANGUAGE TemplateHaskell #-}
module Database.DSH.CompileFlattening (toNKL) where

import Database.DSH.Impossible

import qualified Language.ParallelLang.NKL.Data.NKL as NKL
import qualified Language.ParallelLang.Common.Data.Val as V
import qualified Language.ParallelLang.Common.Data.Type as T
import qualified Language.ParallelLang.Common.Data.Op as O

import Database.DSH.Data as D
import Database.DSH.Impossible (impossible)
import Database.HDBC
import Data.Text (unpack)

import qualified Data.Map as M
import qualified Data.List as L

import Control.Monad.State
import Control.Applicative

import Data.Char (toLower)
{-
N monad, version of the state monad that can provide fresh variable names.
-}
type N conn = StateT (conn, Int, M.Map String [(String, (T.Type -> Bool))]) IO

-- | Lookup information that describes a table. If the information is 
-- not present in the state then the connection is used to retrieve the
-- table information from the Database.
tableInfo :: IConnection conn => String -> N conn [(String, (T.Type -> Bool))]
tableInfo t = do
               (c, i, env) <- get
               case M.lookup t env of
                     Nothing -> do
                                 inf <- lift $ getTableInfo c t
                                 put (c, i, M.insert t inf env)
                                 return inf                                      
                     Just v -> return v

-- | Retrieve through the given database connection information on the table (columns with their types)
-- which name is given as the second argument.        
getTableInfo :: IConnection conn => conn -> String -> IO [(String, (T.Type -> Bool))]
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



-- | Provide a fresh identifier name during compilation
freshVar :: N conn Int
freshVar = do
             (c, i, m) <- get
             put (c, i + 1, m)
             return i

prefixVar :: Int -> String
prefixVar i = "*dshVar*" ++ show i

-- | Get from the state the connection to the database                
getConnection :: IConnection conn => N conn conn
getConnection = do
                 (c, _, _) <- get
                 return c

toNKL :: IConnection conn => conn -> Exp -> IO NKL.Expr
toNKL c e = runN c $ translate e

-- | Execute the transformation computation. During
-- compilation table information can be retrieved from
-- the database, therefor the result is wrapped in the IO
-- Monad.      
runN :: IConnection conn => conn -> N conn a -> IO a
runN c  = liftM fst . flip runStateT (c, 1, M.empty)


translate :: IConnection conn => Exp -> N conn NKL.Expr
translate (UnitE _) = return $ NKL.Const T.unitT V.Unit
translate (BoolE b _) = return $ NKL.Const T.boolT $ V.Bool b
translate (CharE c _) = return $ NKL.Const T.stringT $ V.String [c]
translate (IntegerE i _) = return $ NKL.Const T.intT $ V.Int (fromInteger i)
translate (DoubleE d _) = return $ NKL.Const T.doubleT $ V.Double d 
translate (TextE t _) = return $ NKL.Const T.stringT $ V.String (unpack t) 
translate (VarE i ty) = return $ NKL.Var (ty2ty ty) (prefixVar i)
translate (TableE (TableDB n ks) ty) = do
                                        let ts = zip [1..] $ tableTypes ty
                                        tableDescr <- tableInfo n
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
                                return $ NKL.Tuple (T.pairT t1 t2) [c1, c2]
translate (ListE es ty) = toList (NKL.Const (ty2ty ty) (V.List [])) <$> mapM translate es
translate (LamE f ty) = do
                        v <- freshVar
                        let (ArrowT t1 _) = ty
                        f' <- translate $ f (VarE v t1)
                        return $ NKL.Lam (ty2ty ty) (prefixVar v) f' 
translate (AppE1 Fst e1 ty) = do
                                c1 <- translate e1
                                let t1 = T.typeOf c1
                                return $ NKL.Proj (head $ T.tupleComponents t1) 0 c1 1
translate (AppE1 Snd e1 ty) = do
                                c1 <- translate e1
                                let t1 = T.typeOf c1
                                return $ NKL.Proj (head $ T.tupleComponents t1) 0 c1 2
translate (AppE1 f e1 ty) = do 
                                c1 <- translate e1
                                return $ NKL.App (ty2ty ty) (NKL.Var (T.typeOf c1 T..-> ty2ty ty) (map toLower $ show f)) c1
translate (AppE2 Map e1 e2 ty) = do
                                  c1 <- translate e1
                                  c2 <- translate e2
                                  n <- freshVar
                                  let tEl = T.unliftType (T.typeOf c2)
                                  let tr = T.extractFnRes (T.typeOf c1)
#ifndef withMap
                                  return $ NKL.Iter (ty2ty ty) (prefixVar n) c2 (NKL.App tr c1 (NKL.Var tEl (prefixVar n)))
#else
                                  return $ NKL.App (ty2ty ty) (NKL.App (ty2ty $ ArrowT (typeExp e2) ty) (NKL.Var (ty2ty $ ArrowT (typeExp e1) (ArrowT (typeExp e2) ty)) "map") c1) c2
#endif
translate (AppE2 GroupWith f e ty) = do
                                      c1 <- translate f
                                      c2 <- translate e
                                      return $ NKL.App (ty2ty ty) (NKL.App (ty2ty $ ArrowT (typeExp e) ty) (NKL.Var (ty2ty $  ArrowT (typeExp f) (ArrowT (typeExp e) ty)) "groupWith") c1) c2
translate (AppE2 D.Cons e1 e2 _) = do
                                            e1' <- translate e1
                                            e2' <- translate e2
                                            return $ toList e2' [e1']  
translate (AppE2 f2 e1 e2 ty) = do
                                        let tr = ty2ty ty
                                        if elem f2 [Add, Sub, Mul, Div, Equ, Lt, Gt, Conj, Disj]
                                            then do
                                                   e1' <- translate e1
                                                   e2' <- translate e2
                                                   return $ NKL.BinOp tr (transformOp f2) e1' e2'
                                            else if elem f2 [Lte, Gte] 
                                                    then translate (AppE2 Disj (AppE2 Equ e1 e2 ty) (AppE2 (gtorlt f2) e1 e2 ty) ty)
                                                    else error $"Application2: Not supported yet: " ++ show f2
translate (AppE3 Cond e1 e2 e3 _) = do
                                             e1' <- translate e1
                                             e2' <- translate e2
                                             e3' <- translate e3
                                             return $ NKL.If (T.typeOf e2') e1' e2' e3'


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
        fromTuples t              = [ty2ty t]
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
        primList ((NKL.Const _ v):vs) (NKL.Const ty (V.List es)) = primList vs (NKL.Const ty (V.List (v:es)))
        primList [] e = e
        primList vs (NKL.Const ty (V.List [])) = consList vs (NKL.Nil ty)
        primList vs e = consList vs e
        consList :: [NKL.Expr] -> NKL.Expr -> NKL.Expr
        consList es e = foldl cons e es

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
isPrimVal _ = False
