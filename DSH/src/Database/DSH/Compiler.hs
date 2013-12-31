{-# LANGUAGE TemplateHaskell #-}

-- | This module provides the flattening implementation of DSH.
module Database.DSH.Compiler
  ( -- * Running queries via the Flattening backend
    fromQX100
    -- * Debug functions
  , debugNKL
  , debugFKL
  , debugX100
  , debugCLX100
  , debugNKLX100
  , debugFKLX100
  , debugVL
  , debugX100VL
  , debugTA
  , dumpVLMem
  ) where

import           GHC.Exts
import           Text.Printf
                 
import           Database.DSH.CompileFlattening
import           Database.DSH.ExecuteFlattening

import           Database.DSH.Internals
import           Database.HDBC
import qualified Database.HDBC                                   as H

import           Database.X100Client                             hiding (X100, tableName)
import qualified Database.X100Client                             as X

import           Database.Algebra.Dag

import qualified Database.DSH.CL.Lang                 as CL
import qualified Database.DSH.CL.Opt                  as CLOpt
import           Database.DSH.Common.Data.QueryPlan
import qualified Database.DSH.Common.Data.Type        as T
import           Database.DSH.Export
import           Database.DSH.Optimizer.VL.OptimizeVL
import           Database.DSH.Translate.Algebra2Query
import           Database.DSH.Translate.CL2NKL
import           Database.DSH.Translate.FKL2VL
import           Database.DSH.Translate.NKL2FKL
import           Database.DSH.Translate.VL2Algebra
import qualified Database.DSH.VL.Data.Query           as Q

import           Data.Aeson                                      (encode)
import           Data.ByteString.Lazy.Char8                      (unpack)

import qualified Data.IntMap                                     as M
import qualified Data.List                                       as L

import           Control.Applicative

import           Data.Convertible                                ()

(|>) :: a -> (a -> b) -> b
(|>) = flip ($)

-- Different versions of the flattening compiler pipeline

nkl2X100Alg :: CL.Expr -> (Q.Query Q.X100, T.Type)
nkl2X100Alg e = let q = desugarComprehensions e
                        |> flatten
                        |> specializeVectorOps
                        |> optimizeVLDefault
                        |> implementVectorOpsX100
                        |> generateX100Query
                    t = T.typeOf e
                in (q, t)

nkl2X100File :: String -> CL.Expr -> IO ()
nkl2X100File prefix e = desugarComprehensions e
                        |> flatten
                        |> specializeVectorOps
                        |> optimizeVLDefault
                        |> implementVectorOpsX100
                        |> (exportX100Plan prefix)

nkl2TAFile :: String -> CL.Expr -> IO ()
nkl2TAFile prefix e = desugarComprehensions e
                        |> flatten
                        |> specializeVectorOps
                        |> optimizeVLDefault
                        |> implementVectorOpsPF
                        |> (exportTAPlan prefix)

nkl2VLFile :: String -> CL.Expr -> IO ()
nkl2VLFile prefix e = desugarComprehensions e
                      |> flatten
                      |> specializeVectorOps
                      |> optimizeVLDefault
                      |> exportVLPlan prefix


-- Functions for executing and debugging DSH queries via the Flattening backend

-- | Compile a DSH query to X100 algebra and run it on the X100 server given by 'c'.
fromQX100 :: QA a => X100Info -> Q a -> IO a
fromQX100 c (Q a) =  do
                  (q, _) <- nkl2X100Alg <$> CLOpt.opt <$> toComprehensions (getX100TableInfo c) a
                  frExp <$> (executeX100Query c $ X100 q)
                  
-- | Debugging function: return the CL (Comprehension Language) representation of a
-- query (X100 version)
debugCLX100 :: QA a => X100Info -> Q a -> IO String
debugCLX100 c (Q e) = show <$> CLOpt.opt <$> toComprehensions (getX100TableInfo c) e

-- | Debugging function: return the NKL (Nested Kernel Language) representation of a
-- query (SQL version)
debugNKL :: (QA a, IConnection conn) => conn -> Q a -> IO String
debugNKL c (Q e) = show <$> desugarComprehensions <$> CLOpt.opt <$> toComprehensions (getTableInfo c) e

-- | Debugging function: return the NKL (Nested Kernel Language) representation of a
-- query (X100 version)
debugNKLX100 :: QA a => X100Info -> Q a -> IO String
debugNKLX100 c (Q e) = show <$> desugarComprehensions <$> CLOpt.opt <$> toComprehensions (getX100TableInfo c) e

-- | Debugging function: return the FKL (Flat Kernel Language) representation of a
-- query (SQL version)
debugFKL :: (QA a, IConnection conn) => conn -> Q a -> IO String
debugFKL c (Q e) = show <$> flatten <$> desugarComprehensions <$> toComprehensions (getTableInfo c) e

-- | Debugging function: return the FKL (Flat Kernel Language) representation of a
-- query (X100 version)
debugFKLX100 :: QA a => X100Info -> Q a -> IO String
debugFKLX100 c (Q e) = show <$> flatten <$> desugarComprehensions <$> toComprehensions (getX100TableInfo c) e

-- | Debugging function: dump the X100 plan (DAG) to a file.
debugX100 :: QA a => String -> X100Info -> Q a -> IO ()
debugX100 prefix c (Q e) = do
              e' <- CLOpt.opt <$> toComprehensions (getX100TableInfo c) e
              nkl2X100File prefix e'

-- | Debugging function: dump the table algebra plan (JSON) to a file.
debugTA :: (QA a, IConnection conn) => String -> conn -> Q a -> IO ()
debugTA prefix c (Q e) = do
              e' <- CLOpt.opt <$> toComprehensions (getTableInfo c) e
              nkl2TAFile prefix e'

-- | Debugging function: dump the VL query plan (DAG) for a query to a file (SQL version).
debugVL :: (QA a, IConnection conn) => String -> conn -> Q a -> IO ()
debugVL prefix c (Q e) = do
  e' <- CLOpt.opt <$> toComprehensions (getTableInfo c) e
  nkl2VLFile prefix e'

-- | Debugging function: dump the VL query plan (DAG) for a query to a file (X100 version).
debugX100VL :: QA a => String -> X100Info -> Q a -> IO ()
debugX100VL prefix c (Q e) = do
  e' <- CLOpt.opt <$> toComprehensions (getX100TableInfo c) e
  nkl2VLFile prefix e'

-- | Dump a VL plan in the JSON format expected by the in-memory implementation (Tobias Müller)
dumpVLMem :: QA a => FilePath -> X100Info -> Q a -> IO ()
dumpVLMem f c (Q q) = do
  cl <- toComprehensions (getX100TableInfo c) q
  let plan = desugarComprehensions cl
             |> flatten
             |> specializeVectorOps
      json = unpack $ encode (queryShape plan, M.toList $ nodeMap $ queryDag plan)
  writeFile f json

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
