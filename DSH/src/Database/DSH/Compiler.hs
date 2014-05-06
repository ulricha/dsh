{-# LANGUAGE TemplateHaskell #-}

-- | Compilation, execution and introspection of queries
module Database.DSH.Compiler
  ( -- * Executing queries
    runQ
    -- * Debug functions
  , debugQ
  , debugVL
  , debugVLOpt
  , debugTA
  , debugTAOpt
  , runPrint
  ) where

import           Control.Applicative

import           Database.DSH.CompileFlattening
import           Database.DSH.Execute.Sql

import           Database.DSH.Internals
import qualified Database.HDBC                        as H

import qualified Database.DSH.CL.Lang                 as CL
import           Database.DSH.CL.Opt
import           Database.DSH.Common.DBCode
import           Database.DSH.Common.QueryPlan
import           Database.DSH.Export
import           Database.DSH.Optimizer.TA.OptimizeTA
import           Database.DSH.Optimizer.VL.OptimizeVL
import           Database.DSH.Schema
import           Database.DSH.Translate.Algebra2Query
import           Database.DSH.Translate.CL2NKL
import           Database.DSH.Translate.FKL2VL
import           Database.DSH.Translate.NKL2FKL
import           Database.DSH.Translate.VL2Algebra

(|>) :: a -> (a -> b) -> b
(|>) = flip ($)

-- Different versions of the flattening compiler pipeline

nkl2Sql :: CL.Expr -> TopShape SqlCode
nkl2Sql e =
    optimizeComprehensions e
    |> desugarComprehensions
    |> flatten
    |> specializeVectorOps
    |> optimizeVLDefault
    |> implementVectorOpsPF
    |> optimizeTA
    |> generateSqlQueries

nkl2TAFile :: String -> CL.Expr -> IO ()
nkl2TAFile prefix e =
    optimizeComprehensions e
    |> desugarComprehensions
    |> flatten
    |> specializeVectorOps
    |> optimizeVLDefault
    |> implementVectorOpsPF
    |> (exportTAPlan prefix)

nkl2TAFileOpt :: String -> CL.Expr -> IO ()
nkl2TAFileOpt prefix e =
    optimizeComprehensions e
    |> desugarComprehensions
    |> flatten
    |> specializeVectorOps
    |> optimizeVLDefault
    |> implementVectorOpsPF
    |> optimizeTA
    |> (exportTAPlan prefix)

nkl2VLFile :: String -> CL.Expr -> IO ()
nkl2VLFile prefix e =
    optimizeComprehensions e
    |> desugarComprehensions
    |> flatten
    |> specializeVectorOps
    |> exportVLPlan prefix

nkl2VLFileOpt :: String -> CL.Expr -> IO ()
nkl2VLFileOpt prefix e =
    optimizeComprehensions e
    |> desugarComprehensions
    |> flatten
    |> specializeVectorOps
    |> optimizeVLDefault
    |> exportVLPlan prefix

-- Functions for executing and debugging DSH queries via the Flattening backend

-- | Run a query on a SQL backend
runQ :: (QA a, H.IConnection conn) => conn -> Q a -> IO a
runQ conn (Q q) = do
    let ty = reify (undefined :: a)
    q' <- toComprehensions (getTableInfo conn) q
    let sqlQueryBundle = nkl2Sql q'
    frExp <$> executeSql conn sqlQueryBundle ty

-- | Debugging function: dump the table algebra plan (JSON) to a file.
debugTA :: (QA a, H.IConnection conn) => String -> conn -> Q a -> IO ()
debugTA prefix c (Q e) = do
    e' <- toComprehensions (getTableInfo c) e
    nkl2TAFile prefix e'

-- | Debugging function: dump the optimized table algebra plan (JSON) to a file.
debugTAOpt :: (QA a, H.IConnection conn) => String -> conn -> Q a -> IO ()
debugTAOpt prefix c (Q e) = do
    e' <- toComprehensions (getTableInfo c) e
    nkl2TAFileOpt prefix e'

-- | Debugging function: dump the VL query plan (DAG) for a query to a
-- file (SQL version).
debugVL :: (QA a, H.IConnection conn) => String -> conn -> Q a -> IO ()
debugVL prefix c (Q e) = do
    e' <- toComprehensions (getTableInfo c) e
    nkl2VLFile prefix e'

-- | Debugging function: dump the optimized VL query plan (DAG) for a
-- query to a file (SQL version).
debugVLOpt :: (QA a, H.IConnection conn) => String -> conn -> Q a -> IO ()
debugVLOpt prefix c (Q e) = do
    e' <- toComprehensions (getTableInfo c) e
    nkl2VLFileOpt prefix e'

-- | Dump all intermediate algebra representations (VL, TA) to files.
debugQ :: (QA a, H.IConnection conn) => String -> conn -> Q a -> IO ()
debugQ prefix conn q = do
    debugVLOpt prefix conn q
    debugTAOpt prefix conn q

-- | Convenience function: execute a query on a SQL backend and print
-- its result
runPrint :: (Show a, QA a, H.IConnection conn) => conn -> Q a -> IO ()
runPrint conn q = (show <$> runQ conn q) >>= putStrLn
