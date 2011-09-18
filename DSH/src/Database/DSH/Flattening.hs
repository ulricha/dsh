{-# LANGUAGE TemplateHaskell #-}
-- | This module provides the flattening implementation of DSH.
module Database.DSH.Flattening (fromQ, debugPlan, debugSQL, debugNKL, debugFKL, debugFKL', debugX100, debugX100Plan, debugNKLX100, debugFKLX100) where

import Language.ParallelLang.DBPH hiding (SQL)

import Database.DSH.ExecuteFlattening
import Database.DSH.CompileFlattening

import Database.DSH.Data
import Database.HDBC

import Database.X100Client(X100Info)

import qualified Language.ParallelLang.Common.Data.Type as T

import qualified Data.List as L

import Control.Monad.State

fromQ :: (QA a, IConnection conn) => conn -> Q a -> IO a
fromQ c (Q a) =  do
                   (q, t) <- liftM nkl2SQL $ toNKL (getTableInfo c) a
                   executeSQLQuery c t $ SQL q
                   
debugNKL :: (QA a, IConnection conn) => conn -> Q a -> IO String
debugNKL c (Q e) = liftM show $ toNKL (getTableInfo c) e

debugNKLX100 :: QA a => X100Info -> Q a -> IO String
debugNKLX100 c (Q e) = liftM show $ toNKL (getX100TableInfo c) e

debugFKL :: (QA a, IConnection conn) => conn -> Q a -> IO String
debugFKL c (Q e) = liftM nkl2fkl $ toNKL (getTableInfo c) e

debugFKLX100 :: QA a => X100Info -> Q a -> IO String
debugFKLX100 c (Q e) = liftM nkl2fkl $ toNKL (getX100TableInfo c) e

debugFKL' :: (QA a, IConnection conn) => conn -> Q a -> IO String
debugFKL' c (Q e) = liftM nkl2fkl' $ toNKL (getTableInfo c) e
    
debugX100 :: QA a => X100Info -> Q a -> IO ()
debugX100 c (Q e) = do
              e' <- toNKL (getX100TableInfo c) e
              nkl2X100File "query.plan" e'
              
debugX100Plan :: QA a => X100Info -> Q a -> IO String
debugX100Plan c (Q e) = liftM (show . fst . nkl2X100Alg) $ toNKL (getX100TableInfo c) e

debugPlan :: (QA a, IConnection conn) => conn -> Q a -> IO String
debugPlan c (Q e) = liftM (show . fst . nkl2Alg) $ toNKL (getTableInfo c) e

debugSQL :: (QA a, IConnection conn) => conn -> Q a -> IO String
debugSQL c (Q e) = liftM (show . fst . nkl2SQL) $ toNKL (getTableInfo c) e


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

getX100TableInfo :: X100Info -> String -> IO [(String, (T.Type -> Bool))]
getX100TableInfo _c n = return $ 
                        case n of
                         "employees" -> [("department", \t -> t == T.String), ("name", \t -> t == T.String), ("salary", \t -> t == T.Int)]
