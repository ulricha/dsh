{-# LANGUAGE TemplateHaskell  #-}
module Database.DSH.CompileFlattening (toNKL) where

import Database.DSH.Impossible

import qualified Language.ParallelLang.NKL.NKLPrimitives as NP
-- import qualified Language.ParallelLang.NP.Data.NP as NP
import qualified Language.ParallelLang.Common.Data.Type as T

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

toNKL :: (String -> IO [(String, T.Type -> Bool)]) -> Exp -> IO NP.Expr
toNKL f e = runN f $ translate e

-- | Execute the transformation computation. During
-- compilation table information can be retrieved from
-- the database, therefor the result is wrapped in the IO
-- Monad.      
runN :: (String -> IO [(String, T.Type -> Bool)]) -> N a -> IO a
runN f = liftM fst . flip runStateT (1, M.empty, f)


translate ::  Exp -> N NP.Expr
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
translate (ListE es ty) = NP.list (translateType ty) <$> mapM translate es
translate (LamE f ty) = do
                        v <- freshVar
                        let (ArrowT t1 _) = ty
                        NP.lambda (translateType ty) (prefixVar v) <$> (translate $ f (VarE v t1)) 
translate (AppE1 f e _) = translateFun1 f <$> translate e
translate (AppE2 f2 e1 e2 _) = translateFun2 f2 <$> translate e1 <*> translate e2
translate (AppE3 Cond e1 e2 e3 _) = NP.cond <$> translate e1 <*> translate e2 <*> translate e3
translate (TableE (TableCSV _) _) = $impossible
translate (AppE3 ZipWith _ _ _ _) = $impossible

translateFun2 :: Fun2 -> NP.Expr -> NP.Expr -> NP.Expr
translateFun2 Add       = NP.add
translateFun2 Mul       = NP.mul
translateFun2 Sub       = NP.sub
translateFun2 Div       = NP.div
translateFun2 All       = NP.all
translateFun2 Any       = NP.any
translateFun2 Index     = NP.index
translateFun2 SortWith  = NP.sortWith
translateFun2 Cons      = NP.consOpt
translateFun2 Snoc      = NP.snoc
translateFun2 Take      = NP.take
translateFun2 Drop      = NP.drop
translateFun2 Map       = NP.map
translateFun2 Append    = NP.append
translateFun2 Filter    = NP.filter
translateFun2 GroupWith = NP.groupWith
translateFun2 Zip       = NP.zip
translateFun2 Break     = $impossible
translateFun2 Span      = $impossible
translateFun2 DropWhile = $impossible
translateFun2 TakeWhile = $impossible
translateFun2 SplitAt   = NP.splitAt
translateFun2 Equ       = NP.eq
translateFun2 Conj      = NP.conj
translateFun2 Disj      = NP.disj
translateFun2 Lt        = NP.lt
translateFun2 Lte       = NP.lte
translateFun2 Gte       = NP.gte
translateFun2 Gt        = NP.gt
translateFun2 Max       = $impossible
translateFun2 Min       = $impossible

translateFun1 :: Fun1 -> NP.Expr -> NP.Expr
translateFun1 Fst = NP.fst
translateFun1 Snd = NP.snd
translateFun1 Not = NP.not
translateFun1 IntegerToDouble = NP.integerToDouble
translateFun1 Head = NP.head
translateFun1 Tail = NP.tail
translateFun1 Unzip = NP.unzip
translateFun1 Minimum = NP.minimum
translateFun1 Maximum = NP.maximum
translateFun1 Concat = NP.concat
translateFun1 Sum = NP.sum
translateFun1 And = NP.and
translateFun1 Or = NP.or
translateFun1 Reverse = NP.reverse
translateFun1 Length = NP.length
translateFun1 Null = NP.null
translateFun1 Init = NP.init
translateFun1 Last = NP.last
translateFun1 The = NP.the
translateFun1 Nub = NP.nub

legalType :: String -> String -> Int -> T.Type -> (T.Type -> Bool) -> Bool
legalType tn cn nr t f = case f t of
                            True -> True
                            False -> error $ "The type: " ++ show t ++ "\nis not compatible with the type of column nr: " ++ show nr
                                                ++ " namely: " ++ cn ++ "\n in table " ++ tn ++ "."

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