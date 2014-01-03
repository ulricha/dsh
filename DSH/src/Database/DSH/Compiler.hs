{-# LANGUAGE TemplateHaskell #-}

-- | This module provides the flattening implementation of DSH.
module Database.DSH.Compiler
  ( -- * Debug functions
    debugNKL
  , debugFKL
  , debugVL
  , debugVLOpt
  , debugTA
  , debugTAOpt
  ) where

import           Text.Printf
import           GHC.Exts
import           Database.DSH.CompileFlattening

import           Database.DSH.Internals
import           Database.HDBC
import qualified Database.HDBC                                   as H

import qualified Database.DSH.CL.Lang                 as CL
import qualified Database.DSH.CL.Opt                  as CLOpt
import qualified Database.DSH.Common.Data.Type        as T
import           Database.DSH.Export
import           Database.DSH.Optimizer.VL.OptimizeVL
import           Database.DSH.Optimizer.TA.OptimizeTA
import           Database.DSH.Translate.CL2NKL
import           Database.DSH.Translate.FKL2VL
import           Database.DSH.Translate.NKL2FKL
import           Database.DSH.Translate.VL2Algebra

import qualified Data.List                                       as L

import           Control.Applicative

import           Data.Convertible                                ()

(|>) :: a -> (a -> b) -> b
(|>) = flip ($)

-- Different versions of the flattening compiler pipeline

nkl2TAFile :: String -> CL.Expr -> IO ()
nkl2TAFile prefix e = desugarComprehensions e
                      |> flatten
                      |> specializeVectorOps
                      |> optimizeVLDefault
                      |> implementVectorOpsPF
                      |> (exportTAPlan prefix)

nkl2TAFileOpt :: String -> CL.Expr -> IO ()
nkl2TAFileOpt prefix e = desugarComprehensions e
                         |> flatten
                         |> specializeVectorOps
                         |> optimizeVLDefault
                         |> implementVectorOpsPF
                         |> optimizeTA
                         |> (exportTAPlan prefix)

nkl2VLFile :: String -> CL.Expr -> IO ()
nkl2VLFile prefix e = desugarComprehensions e
                      |> flatten
                      |> specializeVectorOps
                      |> exportVLPlan prefix

nkl2VLFileOpt :: String -> CL.Expr -> IO ()
nkl2VLFileOpt prefix e = desugarComprehensions e
                         |> flatten
                         |> specializeVectorOps
                         |> optimizeVLDefault
                         |> exportVLPlan prefix

-- Functions for executing and debugging DSH queries via the Flattening backend

-- | Debugging function: return the NKL (Nested Kernel Language) representation of a
-- query (SQL version)
debugNKL :: (QA a, IConnection conn) => conn -> Q a -> IO String
debugNKL c (Q e) = show <$> desugarComprehensions <$> CLOpt.opt <$> toComprehensions (getTableInfo c) e

-- | Debugging function: return the FKL (Flat Kernel Language) representation of a
-- query (SQL version)
debugFKL :: (QA a, IConnection conn) => conn -> Q a -> IO String
debugFKL c (Q e) = show <$> flatten <$> desugarComprehensions <$> toComprehensions (getTableInfo c) e

-- | Debugging function: dump the table algebra plan (JSON) to a file.
debugTA :: (QA a, IConnection conn) => String -> conn -> Q a -> IO ()
debugTA prefix c (Q e) = do
              e' <- CLOpt.opt <$> toComprehensions (getTableInfo c) e
              nkl2TAFile prefix e'

-- | Debugging function: dump the optimized table algebra plan (JSON) to a file.
debugTAOpt :: (QA a, IConnection conn) => String -> conn -> Q a -> IO ()
debugTAOpt prefix c (Q e) = do
              e' <- CLOpt.opt <$> toComprehensions (getTableInfo c) e
              nkl2TAFileOpt prefix e'

-- | Debugging function: dump the VL query plan (DAG) for a query to a
-- file (SQL version).
debugVL :: (QA a, IConnection conn) => String -> conn -> Q a -> IO ()
debugVL prefix c (Q e) = do
  e' <- CLOpt.opt <$> toComprehensions (getTableInfo c) e
  nkl2VLFile prefix e'

-- | Debugging function: dump the optimized VL query plan (DAG) for a
-- query to a file (SQL version).
debugVLOpt :: (QA a, IConnection conn) => String -> conn -> Q a -> IO ()
debugVLOpt prefix c (Q e) = do
  e' <- CLOpt.opt <$> toComprehensions (getTableInfo c) e
  nkl2VLFileOpt prefix e'

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
