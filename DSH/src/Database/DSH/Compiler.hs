{-# LANGUAGE TemplateHaskell #-}

-- | This module provides the flattening implementation of DSH.
module Database.DSH.Compiler
  ( -- * Running queries via the Flattening backend
    fromQX100
  , fromQ
    -- * Debug functions
  , debugVL
  , debugVLOpt
  , debugX100VL
  , debugTA
  , debugTAOpt
  ) where

import           GHC.Exts
import           Text.Printf
                 
import           Database.DSH.Impossible
import           Database.DSH.CompileFlattening
import           Database.DSH.ExecuteFlattening

import           Database.DSH.Internals
import           Database.HDBC
import qualified Database.HDBC                                   as H

import           Database.X100Client                             hiding (X100, tableName)
import qualified Database.X100Client                             as X

import qualified Database.DSH.CL.Lang                 as CL
import           Database.DSH.CL.Opt
import           Database.DSH.Common.Data.QueryPlan
import qualified Database.DSH.Common.Data.Type        as T
import           Database.DSH.Export
import           Database.DSH.Optimizer.VL.OptimizeVL
import           Database.DSH.Optimizer.TA.OptimizeTA
import           Database.DSH.Translate.Algebra2Query
import           Database.DSH.Translate.CL2NKL
import           Database.DSH.Translate.FKL2VL
import           Database.DSH.Translate.NKL2FKL
import           Database.DSH.Translate.VL2Algebra
import           Database.DSH.Common.Data.DBCode

import qualified Data.List                                       as L

import           Control.Applicative

import           Data.Convertible                                ()

(|>) :: a -> (a -> b) -> b
(|>) = flip ($)

-- Different versions of the flattening compiler pipeline

nkl2X100Alg :: CL.Expr -> (TopShape X100Code, T.Type)
nkl2X100Alg e = let q = optimizeComprehensions e
                        |> desugarComprehensions
                        |> flatten
                        |> specializeVectorOps
                        |> optimizeVLDefault
                        |> implementVectorOpsX100
                        |> generateX100Query
                    t = T.typeOf e
                in (q, t)

nkl2X100File :: String -> CL.Expr -> IO ()
nkl2X100File prefix e = optimizeComprehensions e
                        |> desugarComprehensions
                        |> flatten
                        |> specializeVectorOps
                        |> optimizeVLDefault
                        |> implementVectorOpsX100
                        |> (exportX100Plan prefix)

nkl2TAFile :: String -> CL.Expr -> IO ()
nkl2TAFile prefix e = optimizeComprehensions e
                      |> desugarComprehensions
                      |> flatten
                      |> specializeVectorOps
                      |> optimizeVLDefault
                      |> implementVectorOpsPF
                      |> (exportTAPlan prefix)

nkl2TAFileOpt :: String -> CL.Expr -> IO ()
nkl2TAFileOpt prefix e = optimizeComprehensions e
                         |> desugarComprehensions
                         |> flatten
                         |> specializeVectorOps
                         |> optimizeVLDefault
                         |> implementVectorOpsPF
                         |> optimizeTA
                         |> (exportTAPlan prefix)

nkl2VLFile :: String -> CL.Expr -> IO ()
nkl2VLFile prefix e = optimizeComprehensions e
                      |> desugarComprehensions
                      |> flatten
                      |> specializeVectorOps
                      |> exportVLPlan prefix

nkl2VLFileOpt :: String -> CL.Expr -> IO ()
nkl2VLFileOpt prefix e = optimizeComprehensions e
                         |> desugarComprehensions
                         |> flatten
                         |> specializeVectorOps
                         |> optimizeVLDefault
                         |> exportVLPlan prefix

-- Functions for executing and debugging DSH queries via the Flattening backend

-- | Compile a DSH query to X100 algebra and run it on the X100 server given by 'c'.
fromQX100 :: QA a => X100Info -> Q a -> IO a
fromQX100 c (Q a) =  undefined
{-
    (q, _) <- nkl2X100Alg <$> toComprehensions (getX100TableInfo c) a
    frExp <$> (executeX100Query c $ X100 q)
-}

fromQ :: (QA a, IConnection conn) => conn -> Q a -> IO a
fromQ c (Q a) = $unimplemented
                  
-- | Debugging function: dump the X100 plan (DAG) to a file.
debugX100 :: QA a => String -> X100Info -> Q a -> IO ()
debugX100 prefix c (Q e) = do
    e' <- toComprehensions (getX100TableInfo c) e
    nkl2X100File prefix e'

-- | Debugging function: dump the table algebra plan (JSON) to a file.
debugTA :: (QA a, IConnection conn) => String -> conn -> Q a -> IO ()
debugTA prefix c (Q e) = do
    e' <- toComprehensions (getTableInfo c) e
    nkl2TAFile prefix e'

-- | Debugging function: dump the optimized table algebra plan (JSON) to a file.
debugTAOpt :: (QA a, IConnection conn) => String -> conn -> Q a -> IO ()
debugTAOpt prefix c (Q e) = do
    e' <- toComprehensions (getTableInfo c) e
    nkl2TAFileOpt prefix e'

-- | Debugging function: dump the VL query plan (DAG) for a query to a
-- file (SQL version).
debugVL :: (QA a, IConnection conn) => String -> conn -> Q a -> IO ()
debugVL prefix c (Q e) = do
    e' <- toComprehensions (getTableInfo c) e
    nkl2VLFile prefix e'

-- | Debugging function: dump the optimized VL query plan (DAG) for a
-- query to a file (SQL version).
debugVLOpt :: (QA a, IConnection conn) => String -> conn -> Q a -> IO ()
debugVLOpt prefix c (Q e) = do
    e' <- toComprehensions (getTableInfo c) e
    nkl2VLFileOpt prefix e'

-- | Debugging function: dump the VL query plan (DAG) for a query to a
-- file (X100 version).
debugX100VL :: QA a => String -> X100Info -> Q a -> IO ()
debugX100VL prefix c (Q e) = do
    e' <- toComprehensions (getX100TableInfo c) e
    nkl2VLFile prefix e'

-- | Retrieve through the given database connection information on the
-- table (columns with their types) which name is given as the second
-- argument.
getTableInfo :: IConnection conn => conn -> String -> IO [(String, String, (T.Type -> Bool))]
getTableInfo conn tableName = do
    info <- H.describeTable conn tableName
    case info of
        []    -> error $ printf "Unknown table %s" tableName
        _ : _ -> return $ toTableDescr info

  where
    toTableDescr :: [(String, SqlColDesc)] -> [(String, String, T.Type -> Bool)]
    toTableDescr cols = sortWith (\(n, _, _) -> n)
                        [ (name, show colTy, compatibleType colTy) 
                        | (name, props) <- cols
                        , let colTy = colType props
                        ]
                        

    compatibleType :: SqlTypeId -> T.Type -> Bool
    compatibleType dbT hsT = 
        case hsT of
            T.UnitT   -> True
            T.BoolT   -> L.elem dbT [SqlSmallIntT, SqlIntegerT, SqlBitT]
            T.StringT -> L.elem dbT [SqlCharT, SqlWCharT, SqlVarCharT]
            T.IntT    -> L.elem dbT [SqlSmallIntT, SqlIntegerT, SqlTinyIntT, SqlBigIntT, SqlNumericT]
            T.DoubleT -> L.elem dbT [SqlDecimalT, SqlRealT, SqlFloatT, SqlDoubleT]
            t         -> error $ printf "Unsupported column type %s for table %s" (show t) (show tableName)

getX100TableInfo :: X100Info -> String -> IO [(String, String, (T.Type -> Bool))]
getX100TableInfo c n = do
    t <- X.describeTable' c n
    return [ (colName col, show lType, compatibleType lType)
           | col <- sortWith colName $ columns t
           , let lType = logicalType col
           ]
  where
    compatibleType :: LType -> T.Type -> Bool
    compatibleType lt t =
        case lt of
            LBool       -> t == T.BoolT || t == T.UnitT
            LInt1       -> t == T.IntT  || t == T.UnitT
            LUInt1      -> t == T.IntT  || t == T.UnitT
            LInt2       -> t == T.IntT  || t == T.UnitT
            LUInt2      -> t == T.IntT  || t == T.UnitT
            LInt4       -> t == T.IntT  || t == T.UnitT
            LUInt4      -> t == T.IntT  || t == T.UnitT
            LInt8       -> t == T.IntT  || t == T.UnitT
            LUInt8      -> t == T.IntT  || t == T.UnitT
            LInt16      -> t == T.IntT  || t == T.UnitT
            LUIDX       -> t == T.NatT  || t == T.UnitT
            LDec        -> t == T.DoubleT
            LFlt4       -> t == T.DoubleT
            LFlt8       -> t == T.DoubleT
            LMoney      -> t == T.DoubleT
            LChar       -> t == T.StringT
            LVChar      -> t == T.StringT
            LDate       -> t == T.IntT
            LTime       -> t == T.IntT
            LTimeStamp  -> t == T.IntT
            LIntervalDS -> t == T.IntT
            LIntervalYM -> t == T.IntT
            LUnknown s  -> error $ "Unknown DB type" ++ show s
