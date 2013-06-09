{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts    #-}

module Database.DSH.CompileFlattening (toNKL) where

import           Database.DSH.Impossible

import qualified Database.DSH.Flattening.NKL.NKLPrimitives as NP
import           Database.DSH.Flattening.NKL.Opt
import qualified Database.DSH.Flattening.Common.Data.Type as T

import           Database.DSH.Internals as D
import           Data.Text (unpack)

import qualified Data.Map as M

import           Control.Monad
import           Control.Monad.State
import           Control.Applicative
       
import           Text.Printf
  
import           GHC.Exts(sortWith)

{-
N monad, version of the state monad that can provide fresh variable names.
-}
type N = StateT (Integer, M.Map String [(String, (T.Type -> Bool))], String -> IO [(String, T.Type -> Bool)]) IO

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
freshVar :: N Integer
freshVar = do
             (i, m, f) <- get
             put (i + 1, m, f)
             return i

prefixVar :: Integer -> String
prefixVar i = "*dshVar*" ++ show i

getTableInfoFun :: String -> N [(String, T.Type -> Bool)]
getTableInfoFun n = do
                   (_, _, f) <- get
                   lift $ f n

toNKL :: (String -> IO [(String, T.Type -> Bool)]) -> Exp a -> IO NP.Expr
toNKL f e = liftM opt $ runN f $ translate e

-- | Execute the transformation computation. During
-- compilation table information can be retrieved from
-- the database, therefor the result is wrapped in the IO
-- Monad.
runN :: (String -> IO [(String, T.Type -> Bool)]) -> N a -> IO a
runN f = liftM fst . flip runStateT (1, M.empty, f)


translate ::  forall a. Exp a -> N NP.Expr
translate UnitE = return $ NP.unit
translate (BoolE b) = return $ NP.bool b
translate (CharE c) = return $ NP.string [c]
translate (IntegerE i) = return $ NP.int (fromInteger i)
translate (DoubleE d) = return $ NP.double d
translate (TextE t) = return $ NP.string (unpack t)
translate (PairE e1 e2) = NP.pair <$> translate e1 <*> translate e2
translate (VarE i) = do
                      let ty = reify (undefined :: a)
                      return $ NP.var (translateType ty) (prefixVar i)
translate (ListE es) = do
                        let ty = reify (undefined :: a)
                        NP.list (translateType ty) <$> mapM translate es
translate (e@(LamE _)) = case e of
                             (LamE f :: Exp (b -> c)) -> do
                                 v <- freshVar
                                 let ty = ArrowT (reify (undefined :: b)) (reify (undefined :: c))
                                 NP.lambda (translateType ty) (prefixVar v) <$> (translate $ f (VarE v :: Exp b))
                             _ -> $impossible
translate (TableE (TableDB n ks)) = do
                                        let ty = reify (undefined :: a)
                                        let ts = zip [1..] $ tableTypes ty
                                        tableDescr <- liftM (sortWith fst) $ tableInfo n
                                        let tyDescr = if length tableDescr == length ts
                                                        then zip tableDescr ts
                                                        else error $ printf "Inferred type\n%s doesn't match type of table %s\n%s\n%d %d" (show ts) n (show $ map fst tableDescr) (length tableDescr) (length ts)
                                        let cols = [(cn, t) | ((cn, f), (i, t)) <- tyDescr, legalType n cn i t f]
                                        let ks' = if ks == []
                                                    then [map fst tableDescr]
                                                    else ks
                                        return $ NP.table (translateType ty) n cols ks'
translate (TableE (TableCSV _)) = $impossible
translate (AppE f args) = compileApp f args

compileApp3 :: (NP.Expr -> NP.Expr -> NP.Expr -> NP.Expr) -> Exp (a, (b, c)) -> N NP.Expr
compileApp3 f (PairE e1 (PairE e2 e3)) = f <$> translate e1 <*> translate e2 <*> translate e3
compileApp3 _ _ = $impossible

compileApp2 :: (NP.Expr -> NP.Expr -> NP.Expr) -> Exp (a, b) -> N NP.Expr
compileApp2 f (PairE e1 e2) = f <$> translate e1 <*> translate e2
compileApp2 _ _ = $impossible

compileApp1 :: (NP.Expr -> NP.Expr) -> Exp a -> N NP.Expr
compileApp1 f e = f <$> translate e

compileApp :: Fun a b -> Exp a -> N NP.Expr
compileApp f args = case f of
                        Cond -> compileApp3 NP.cond args
                        Add       -> compileApp2 NP.add args
                        Mul       -> compileApp2 NP.mul args
                        Sub       -> compileApp2 NP.sub args
                        Div       -> compileApp2 NP.div args
                        Mod       -> compileApp2 NP.mod args
                        Index     -> compileApp2 NP.index args
                        SortWith  -> compileApp2 NP.sortWith args
                        Cons      -> compileApp2 NP.consOpt args
                        Take      -> compileApp2 NP.take args
                        Drop      -> compileApp2 NP.drop args
                        Map       -> compileApp2 NP.map args
                        Append    -> compileApp2 NP.append args
                        Filter    -> compileApp2 NP.filter args
                        GroupWithKey -> compileApp2 NP.groupWithKey args
                        Zip       -> compileApp2 NP.zip args
                        DropWhile -> compileApp2 NP.dropWhile args
                        TakeWhile -> compileApp2 NP.takeWhile args
                        SplitAt   -> compileApp2 NP.splitAt args
                        Equ       -> compileApp2 NP.eq args
                        Conj      -> compileApp2 NP.conj args
                        Disj      -> compileApp2 NP.disj args
                        Lt        -> compileApp2 NP.lt args
                        Lte       -> compileApp2 NP.lte args
                        Gte       -> compileApp2 NP.gte args
                        Gt        -> compileApp2 NP.gt args
                        Max       -> compileApp2 NP.max args
                        Min       -> compileApp2 NP.min args
                        Like      -> compileApp2 NP.like args
                        Fst             -> compileApp1 NP.fst args
                        Snd             -> compileApp1 NP.snd args
                        Not             -> compileApp1 NP.not args
                        IntegerToDouble -> compileApp1 NP.integerToDouble args
                        Head            -> compileApp1 NP.head args
                        Tail            -> compileApp1 NP.tail args
                        Minimum         -> compileApp1 NP.minimum args
                        Maximum         -> compileApp1 NP.maximum args
                        Concat          -> compileApp1 NP.concat args
                        Sum             -> compileApp1 NP.sum args
                        Avg             -> compileApp1 NP.avg args
                        And             -> compileApp1 NP.and args
                        Or              -> compileApp1 NP.or args
                        Reverse         -> compileApp1 NP.reverse args
                        Number          -> compileApp1 NP.number args
                        Length          -> compileApp1 NP.length args
                        Null            -> compileApp1 NP.null args
                        Init            -> compileApp1 NP.init args
                        Last            -> compileApp1 NP.last args
                        Nub             -> compileApp1 NP.nub args

legalType :: String -> String -> Int -> T.Type -> (T.Type -> Bool) -> Bool
legalType tn cn nr t f = case f t of
                            True -> True
                            False -> error $ "The type: " ++ show t ++ "\nis not compatible with the type of column nr: " ++ show nr
                                                ++ " namely: " ++ cn ++ "\n in table " ++ tn ++ "."

translateType :: Type a -> T.Type
translateType UnitT = T.unitT
translateType BoolT = T.boolT
translateType CharT = T.stringT
translateType IntegerT = T.intT
translateType DoubleT = T.doubleT
translateType TextT = T.stringT
translateType (PairT t1 t2) = T.pairT (translateType t1) (translateType t2)
translateType (ListT t) = T.listT (translateType t)
translateType (ArrowT t1 t2) = (translateType t1) T..-> (translateType t2)

tableTypes :: Type [a] -> [T.Type]
tableTypes (ListT t) = fromTuples t
    where
        fromTuples :: Type a -> [T.Type]
        fromTuples (PairT t1 t2) = translateType t1 : fromTuples t2
        fromTuples t'              = [translateType t']
