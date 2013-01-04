{-# LANGUAGE TemplateHaskell #-}
-- | This module provides the flattening implementation of DSH.
module Database.DSH.Flattening (fromQ, debugPlan, debugSQL, debugNKL, debugFKL, fromX100, debugX100, debugX100Plan, debugNKLX100, debugFKLX100, debugVL, debugX100VL, debugX100VLRaw) where

import           GHC.Exts

import           Database.DSH.Flattening.DBPH              hiding (SQL, X100)

import           Database.DSH.CompileFlattening
import           Database.DSH.ExecuteFlattening

import           Database.DSH.Internals
import           Database.HDBC
import qualified Database.HDBC                             as H

import           Database.X100Client                       hiding (X100)
import qualified Database.X100Client                       as X

import qualified Database.DSH.Flattening.Common.Data.Type  as T
import           Database.DSH.Flattening.Translate.NKL2FKL

import qualified Data.List                                 as L

import           Control.Monad.State

import           Data.Convertible                          ()
{-
fromQ :: (QA a, IConnection conn) => conn -> Q a -> IO a
fromQ c (Q e) = fmap frExp (evaluate c e)
-}

fromQ :: (QA a, IConnection conn) => conn -> Q a -> IO a
fromQ c (Q a) =  do
                   (q, _) <- liftM nkl2SQL $ toNKL (getTableInfo c) a
                   fmap frExp $ executeSQLQuery c $ SQL q

fromX100 :: QA a => X100Info -> Q a -> IO a
fromX100 c (Q a) =  do
                  (q, _) <- liftM nkl2X100Alg $ toNKL (getX100TableInfo c) a
                  fmap frExp $ executeX100Query c $ X100 q

debugNKL :: (QA a, IConnection conn) => conn -> Q a -> IO String
debugNKL c (Q e) = liftM show $ toNKL (getTableInfo c) e

debugNKLX100 :: QA a => X100Info -> Q a -> IO String
debugNKLX100 c (Q e) = liftM (show . flatten) $ toNKL (getX100TableInfo c) e

debugFKL :: (QA a, IConnection conn) => conn -> Q a -> IO String
debugFKL c (Q e) = liftM (show . flatten) $ toNKL (getTableInfo c) e

debugFKLX100 :: QA a => X100Info -> Q a -> IO String
debugFKLX100 c (Q e) = liftM (show . flatten) $ toNKL (getX100TableInfo c) e

debugX100 :: QA a => X100Info -> Q a -> IO ()
debugX100 c (Q e) = do
              e' <- toNKL (getX100TableInfo c) e
              nkl2X100File "query.plan" e'

debugX100Plan :: QA a => X100Info -> Q a -> IO String
debugX100Plan c (Q e) = liftM (show . fst . nkl2X100Alg) $ toNKL (getX100TableInfo c) e

debugVL :: (QA a, IConnection conn) => conn -> Q a -> IO ()
debugVL c (Q e) = do
  e' <- toNKL (getTableInfo c) e
  nkl2VLFile "query" e'

debugX100VL :: QA a => X100Info -> Q a -> IO ()
debugX100VL c (Q e) = do
  e' <- toNKL (getX100TableInfo c) e
  nkl2VLFile "query" e'

debugX100VLRaw :: QA a => X100Info -> String -> Q a -> IO ()
debugX100VLRaw c f (Q e) = do
    e' <- toNKL (getX100TableInfo c) e
    let s = nkl2VLRaw e'
    writeFile f s

debugPlan :: (QA a, IConnection conn) => conn -> Q a -> IO String
debugPlan c (Q e) = liftM (show . fst . nkl2Alg) $ toNKL (getTableInfo c) e

debugSQL :: (QA a, IConnection conn) => conn -> Q a -> IO String
debugSQL c (Q e) = liftM (show . fst . nkl2SQL) $ toNKL (getTableInfo c) e


-- | Retrieve through the given database connection information on the table (columns with their types)
-- which name is given as the second argument.
getTableInfo :: IConnection conn => conn -> String -> IO [(String, (T.Type -> Bool))]
getTableInfo c n = do
                 info <- H.describeTable c n
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
getX100TableInfo c n = do
                         t <- X.describeTable' c n
                         return [ col2Val col | col <- sortWith colName $ columns t]
        where
            col2Val :: ColumnInfo -> (String, T.Type -> Bool)
            col2Val col = (colName col, \t -> case logicalType col of
                                                LBool       -> t == T.Bool || t == T.Unit
                                                LInt1       -> t == T.Int  || t == T.Unit
                                                LUInt1      -> t == T.Int  || t == T.Unit
                                                LInt2       -> t == T.Int  || t == T.Unit
                                                LUInt2      -> t == T.Int  || t == T.Unit
                                                LInt4       -> t == T.Int  || t == T.Unit
                                                LUInt4      -> t == T.Int  || t == T.Unit
                                                LInt8       -> t == T.Int  || t == T.Unit
                                                LUInt8      -> t == T.Int  || t == T.Unit
                                                LInt16      -> t == T.Int  || t == T.Unit
                                                LUIDX       -> t == T.Nat  || t == T.Unit
                                                LDec        -> t == T.Double
                                                LFlt4       -> t == T.Double
                                                LFlt8       -> t == T.Double
                                                LMoney      -> t == T.Double
                                                LChar       -> t == T.String
                                                LVChar      -> t == T.String
                                                LDate       -> t == T.Int
                                                LTime       -> t == T.Int
                                                LTimeStamp  -> t == T.Int
                                                LIntervalDS -> t == T.Int
                                                LIntervalYM -> t == T.Int
                                                LUnknown s  -> error $ "Unknown DB type" ++ show s)

