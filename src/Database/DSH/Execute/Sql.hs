{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}
{-# LANGUAGE GADTs             #-}

-- | This module implements the execution of SQL query bundles and the
-- construction of nested values from the resulting vector bundle.
module Database.DSH.Execute.Sql
  ( executeSql
  , SqlBackend(..)
  , BackendCode(..)
  ) where

import           Text.Printf

import           Database.HDBC
import           Database.HDBC.PostgreSQL

import qualified Data.Text                             as Txt
import qualified Data.Text.Encoding                    as Txt
import qualified Data.Map as M
import           Control.Monad
import           Control.Applicative

import           Database.DSH.Impossible
import           Database.DSH.Frontend.Internals
import           Database.DSH.Execute.Backend

import           Database.DSH.Common.QueryPlan

newtype SqlBackend = SqlBackend Connection

instance Backend SqlBackend where
    data BackendRow SqlBackend  = SqlRow (M.Map String SqlValue)
    data BackendCode SqlBackend = SqlCode String

    execFlatQuery (SqlBackend conn) (SqlCode q) = do
        stmt  <- prepare conn q
        void $ execute stmt []
        map SqlRow <$> fetchAllRowsMap' stmt

instance Row (BackendRow SqlBackend) where
    data Scalar (BackendRow SqlBackend) = SqlScalar SqlValue

    col c (SqlRow r) = 
        case M.lookup c r of
            Just v  -> SqlScalar v
            Nothing -> error $ printf "col lookup %s failed in %s" c (show r)

    descrVal (SqlScalar (SqlInt32 i))   = fromIntegral i
    descrVal (SqlScalar (SqlInteger i)) = fromIntegral i
    descrVal _                          = $impossible

    scalarVal (SqlScalar SqlNull)           UnitT    = UnitE
    scalarVal (SqlScalar (SqlInteger _))    UnitT    = UnitE
    scalarVal (SqlScalar (SqlInteger i))    IntegerT = IntegerE i
    scalarVal (SqlScalar (SqlInt32 i))      IntegerT = IntegerE $ fromIntegral i
    scalarVal (SqlScalar (SqlInt64 i))      IntegerT = IntegerE $ fromIntegral i
    scalarVal (SqlScalar (SqlWord32 i))     IntegerT = IntegerE $ fromIntegral i
    scalarVal (SqlScalar (SqlWord64 i))     IntegerT = IntegerE $ fromIntegral i
    scalarVal (SqlScalar (SqlDouble d))     DoubleT  = DoubleE d
    scalarVal (SqlScalar (SqlRational d))   DoubleT  = DoubleE $ fromRational d
    scalarVal (SqlScalar (SqlInteger d))    DoubleT  = DoubleE $ fromIntegral d
    scalarVal (SqlScalar (SqlInt32 d))      DoubleT  = DoubleE $ fromIntegral d
    scalarVal (SqlScalar (SqlInt64 d))      DoubleT  = DoubleE $ fromIntegral d
    scalarVal (SqlScalar (SqlWord32 d))     DoubleT  = DoubleE $ fromIntegral d
    scalarVal (SqlScalar (SqlWord64 d))     DoubleT  = DoubleE $ fromIntegral d
    scalarVal (SqlScalar (SqlBool b))       BoolT    = BoolE b
    scalarVal (SqlScalar (SqlInteger i))    BoolT    = BoolE (i /= 0)
    scalarVal (SqlScalar (SqlInt32 i))      BoolT    = BoolE (i /= 0)
    scalarVal (SqlScalar (SqlInt64 i))      BoolT    = BoolE (i /= 0)
    scalarVal (SqlScalar (SqlWord32 i))     BoolT    = BoolE (i /= 0)
    scalarVal (SqlScalar (SqlWord64 i))     BoolT    = BoolE (i /= 0)
    scalarVal (SqlScalar (SqlChar c))       CharT    = CharE c
    scalarVal (SqlScalar (SqlString (c:_))) CharT    = CharE c
    scalarVal (SqlScalar (SqlByteString c)) CharT    = CharE (head $ Txt.unpack $ Txt.decodeUtf8 c)
    scalarVal (SqlScalar (SqlString t))     TextT    = TextE (Txt.pack t)
    scalarVal (SqlScalar (SqlByteString s)) TextT    = TextE (Txt.decodeUtf8 s)
    scalarVal (SqlScalar sql)               _        = error $ "Unsupported SqlValue: "  ++ show sql

-- | Execute a SQL query bundle on PostgreSQL.
executeSql :: SqlBackend -> Shape (BackendCode SqlBackend) -> Type a -> IO (Exp a)
executeSql = execQueryBundle
