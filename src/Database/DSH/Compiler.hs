{-# LANGUAGE TemplateHaskell #-}

-- | Compilation, execution and introspection of queries
module Database.DSH.Compiler
  ( -- * Executing queries
    runQX100
  , runQ
    -- * Debug functions
  , debugQ
  , debugQX100
  , debugVL
  , debugVLOpt
  , debugX100VL
  , debugX100VLOpt
  , debugX100
  , debugX100Opt
  , debugTA
  , debugTAOpt
  , runPrint
  ) where

import           Control.Applicative
import           Control.Arrow

import qualified Database.HDBC                            as H

import           Database.X100Client                      hiding (X100, tableName)

import           Database.DSH.Translate.Frontend2CL
import           Database.DSH.Execute.Sql
import           Database.DSH.Execute.X100

import qualified Database.DSH.VL.Lang                     as VL
import           Database.DSH.VL.Vector
import           Database.DSH.NKL.Rewrite
import qualified Database.DSH.CL.Lang                     as CL
import           Database.DSH.CL.Opt
import           Database.DSH.Common.DBCode
import           Database.DSH.Common.QueryPlan
import           Database.DSH.Export
import           Database.DSH.Frontend.Internals
import           Database.DSH.Optimizer.TA.OptimizeTA
import           Database.DSH.Optimizer.VL.OptimizeVL
import           Database.DSH.Optimizer.X100.OptimizeX100
import           Database.DSH.Frontend.Schema
import           Database.DSH.Translate.Algebra2Query
import           Database.DSH.Translate.CL2NKL
import           Database.DSH.Translate.FKL2VL
import           Database.DSH.Translate.NKL2FKL
import           Database.DSH.Translate.VL2Algebra

--------------------------------------------------------------------------------
-- Different versions of the flattening compiler pipeline

-- | Backend-agnostic part of the pipeline.
commonPipeline :: CL.Expr -> QueryPlan VL.VL VLDVec
commonPipeline =
    optimizeComprehensions
    >>> desugarComprehensions
    >>> optimizeNKL
    >>> flatTransform
    >>> specializeVectorOps

nkl2X100Alg :: CL.Expr -> Shape X100Code
nkl2X100Alg =
    commonPipeline
    >>> optimizeVLDefault
    >>> implementVectorOpsX100
    >>> optimizeX100Default
    >>> generateX100Queries

nkl2Sql :: CL.Expr -> Shape SqlCode
nkl2Sql =
    commonPipeline
    >>> optimizeVLDefault
    >>> implementVectorOpsPF
    >>> optimizeTA
    >>> generateSqlQueries

nkl2X100File :: String -> CL.Expr -> IO ()
nkl2X100File prefix =
    commonPipeline
    >>> optimizeVLDefault
    >>> implementVectorOpsX100
    >>> (exportX100Plan prefix)

nkl2X100FileOpt :: String -> CL.Expr -> IO ()
nkl2X100FileOpt prefix =
    commonPipeline
    >>> optimizeVLDefault
    >>> implementVectorOpsX100
    >>> optimizeX100Default
    >>> exportX100Plan prefix

nkl2TAFile :: String -> CL.Expr -> IO ()
nkl2TAFile prefix =
    commonPipeline
    >>> optimizeVLDefault
    >>> implementVectorOpsPF
    >>> (exportTAPlan prefix)

nkl2TAFileOpt :: String -> CL.Expr -> IO ()
nkl2TAFileOpt prefix =
    commonPipeline
    >>> optimizeVLDefault
    >>> implementVectorOpsPF
    >>> optimizeTA
    >>> exportTAPlan (prefix ++ "_opt")

nkl2VLFile :: String -> CL.Expr -> IO ()
nkl2VLFile prefix = commonPipeline >>> exportVLPlan prefix

nkl2VLFileOpt :: String -> CL.Expr -> IO ()
nkl2VLFileOpt prefix =
    commonPipeline
    >>> optimizeVLDefault
    >>> exportVLPlan (prefix ++ "_opt")

--------------------------------------------------------------------------------
-- Functions for executing and debugging DSH queries via the Flattening backend

-- | Compile a DSH query to X100 algebra and run it on the X100 server given by 'c'.
runQX100 :: QA a => X100Info -> Q a -> IO a
runQX100 conn (Q q) = do
    let ty = reify (undefined :: a)
    q' <- toComprehensions (getX100TableInfo conn) q
    let x100QueryBundle = nkl2X100Alg q'
    frExp <$> executeX100 conn x100QueryBundle ty

-- | Run a query on a SQL backend
runQ :: (QA a, H.IConnection conn) => conn -> Q a -> IO a
runQ conn (Q q) = do
    let ty = reify (undefined :: a)
    q' <- toComprehensions (getTableInfo conn) q
    let sqlQueryBundle = nkl2Sql q'
    frExp <$> executeSql conn sqlQueryBundle ty

-- | Debugging function: dump the X100 plan (DAG) to a file.
debugX100 :: QA a => String -> X100Info -> Q a -> IO ()
debugX100 prefix c (Q e) = do
    e' <- toComprehensions (getX100TableInfo c) e
    nkl2X100File prefix e'

-- | Debugging function: dump the optimized X100 plan (DAG) to a file.
debugX100Opt :: QA a => String -> X100Info -> Q a -> IO ()
debugX100Opt prefix c (Q e) = do
    e' <- toComprehensions (getX100TableInfo c) e
    nkl2X100FileOpt (prefix ++ "_opt") e'

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

-- | Debugging function: dump the optimized VL query plan (DAG) for a
-- query to a file (X100 version).
debugX100VLOpt :: QA a => String -> X100Info -> Q a -> IO ()
debugX100VLOpt prefix c (Q e) = do
    e' <- toComprehensions (getX100TableInfo c) e
    nkl2VLFileOpt prefix e'

-- | Debugging function: dump the VL query plan (DAG) for a query to a
-- file (X100 version).
debugX100VL :: QA a => String -> X100Info -> Q a -> IO ()
debugX100VL prefix c (Q e) = do
    e' <- toComprehensions (getX100TableInfo c) e
    nkl2VLFile prefix e'

-- | Dump all intermediate algebra representations (VL, TA) to files.
debugQ :: (QA a, H.IConnection conn) => String -> conn -> Q a -> IO ()
debugQ prefix conn q = do
    debugVL prefix conn q
    debugVLOpt prefix conn q
    debugTA prefix conn q
    debugTAOpt prefix conn q

-- | Dump all intermediate algebra representations (VL, X100) to files
debugQX100 :: QA a => String -> X100Info -> Q a -> IO ()
debugQX100 prefix conn q = do
    debugX100VL prefix conn q
    debugX100VLOpt prefix conn q
    debugX100 prefix conn q
    debugX100Opt prefix conn q

-- | Convenience function: execute a query on a SQL backend and print
-- its result
runPrint :: (Show a, QA a, H.IConnection conn) => conn -> Q a -> IO ()
runPrint conn q = (show <$> runQ conn q) >>= putStrLn

