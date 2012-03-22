{-# LANGUAGE TemplateHaskell, RelaxedPolyRec, FlexibleInstances, UndecidableInstances  #-}
module Database.DSH.CompileFlattening (toNKL) where

import Database.DSH.Impossible

import qualified Language.ParallelLang.NKL.Primitives as NP
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

{-
N monad, version of the state monad that can provide fresh variable names.
-}
type N = StateT (Int, M.Map String [(String, (T.Type -> Bool))], String -> IO [(String, T.Type -> Bool)]) IO

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
translate (UnitE _) = return $ NP.unit
translate (BoolE b _) = return $ NP.bool b
translate (CharE c _) = return $ NP.string [c]
translate (IntegerE i _) = return $ NP.int (fromInteger i)
translate (DoubleE d _) = return $ NP.double d 
translate (TextE t _) = return $ NP.string (unpack t) 
translate (VarE i ty) = return $ NP.var (translateType ty) (prefixVar i)
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
                                        return $ NP.table (translateType ty) n cols ks'
translate (TupleE e1 e2 _) = NP.pair <$> translate e1 <*> translate e2
translate (ListE es ty) = toList (NKL.Const (translateType ty) (V.List [])) <$> mapM translate es
translate (LamE f ty) = do
                        v <- freshVar
                        let (ArrowT t1 _) = ty
                        NP.lambda (translateType ty) (prefixVar v) <$> (translate $ f (VarE v t1)) 
translate (AppE1 f e _) = translateFun1 f <$> translate e
translate (AppE2 D.Cons e1 e2 _) = do
                                            e1' <- translate e1
                                            e2' <- translate e2
                                            return $ toList e2' [e1']  
translate (AppE2 f2 e1 e2 _) = translateFun2 f2 <$> translate e1 <*> translate e2
translate (AppE3 Cond e1 e2 e3 _) = do
                                             e1' <- translate e1
                                             e2' <- translate e2
                                             e3' <- translate e3
                                             return $ NKL.If (T.typeOf e2') e1' e2' e3'
translate (TableE (TableCSV _) _) = $impossible
translate (AppE3 ZipWith _ _ _ _) = $impossible

translateFun2 :: Fun2 -> NKL.Expr -> NKL.Expr -> NKL.Expr
translateFun2 Add       = NP.add
translateFun2 Mul       = NP.mul
translateFun2 Sub       = NP.sub
translateFun2 Div       = NP.div
translateFun2 All       = $impossible
translateFun2 Any       = $impossible
translateFun2 Index     = $impossible
translateFun2 SortWith  = NP.sortWith
translateFun2 Cons      = NP.cons
translateFun2 Snoc      = $impossible
translateFun2 Take      = $impossible
translateFun2 Drop      = $impossible
translateFun2 Map       = NP.map
translateFun2 Append    = $impossible
translateFun2 Filter    = $impossible
translateFun2 GroupWith = NP.groupWith
translateFun2 Zip       = $impossible
translateFun2 Break     = $impossible
translateFun2 Span      = $impossible
translateFun2 DropWhile = $impossible
translateFun2 TakeWhile = $impossible
translateFun2 SplitAt   = $impossible
translateFun2 Equ       = NP.eq
translateFun2 Conj      = NP.conj
translateFun2 Disj      = NP.disj
translateFun2 Lt        = NP.lt
translateFun2 Lte       = NP.lte
translateFun2 Gte       = NP.gte
translateFun2 Gt        = NP.gt
translateFun2 Max       = $impossible
translateFun2 Min       = $impossible

translateFun1 :: Fun1 -> NKL.Expr -> NKL.Expr
translateFun1 Fst = NP.fst
translateFun1 Snd = NP.snd
translateFun1 Not = NP.not
translateFun1 IntegerToDouble = $impossible
translateFun1 Head = $impossible
translateFun1 Tail = $impossible
translateFun1 Unzip = $impossible
translateFun1 Minimum = $impossible
translateFun1 Maximum = $impossible
translateFun1 Concat = NP.concat
translateFun1 Sum = NP.sum
translateFun1 And = $impossible
translateFun1 Or = $impossible
translateFun1 Reverse = $impossible
translateFun1 Length = NP.length
translateFun1 Null = $impossible
translateFun1 Init = $impossible
translateFun1 Last = $impossible
translateFun1 The = NP.the
translateFun1 Nub = $impossible

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

translateType :: Type -> T.Type
translateType UnitT = T.unitT
translateType BoolT = T.boolT
translateType CharT = T.stringT 
translateType IntegerT = T.intT
translateType DoubleT = T.doubleT
translateType TextT = T.stringT
translateType (TupleT t1 t2) = T.pairT (translateType t1) (translateType t2)
translateType (ListT t) = T.listT (translateType t)
translateType (ArrowT t1 t2) = (translateType t1) T..-> (translateType t2)

tableTypes :: Type -> [T.Type]
tableTypes (ListT t) = fromTuples t
    where
        fromTuples :: Type -> [T.Type]
        fromTuples (TupleT t1 t2) = translateType t1 : fromTuples t2
        fromTuples t'              = [translateType t']
tableTypes _         = $impossible

toList :: NKL.Expr -> [NKL.Expr] -> NKL.Expr
toList n es = primList (reverse es) n 
    where
        primList :: [NKL.Expr] -> NKL.Expr -> NKL.Expr
        primList ((NKL.Const _ v):vs) (NKL.Const ty (V.List xs)) = primList vs (NKL.Const ty (V.List (v:xs)))
        primList [] e = e
        primList vs c@(NKL.Const _ (V.List [])) = consList vs c
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
