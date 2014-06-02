{-# LANGUAGE TemplateHaskell #-}

-- | This module contains functionality to retrieve information about
-- the schema of actual database tables.
module Database.DSH.Schema
    ( getTableInfo
    ) where

import qualified Data.List                as L
import           GHC.Exts
import           Text.Printf

import qualified Database.HDBC            as H

import qualified Database.DSH.Common.Type as T

-- | Retrieve through the given database connection information on the
-- table (columns with their types) which name is given as the second
-- argument.
getTableInfo :: H.IConnection conn => conn -> String -> IO [(String, String, (T.Type -> Bool))]
getTableInfo conn tableName = do
    info <- H.describeTable conn tableName
    case info of
        []    -> error $ printf "Unknown table %s" tableName
        _ : _ -> return $ toTableDescr info

  where
    toTableDescr :: [(String, H.SqlColDesc)] -> [(String, String, T.Type -> Bool)]
    toTableDescr cols = sortWith (\(n, _, _) -> n)
                        [ (name, show colTy, compatibleType colTy)
                        | (name, props) <- cols
                        , let colTy = H.colType props
                        ]


    compatibleType :: H.SqlTypeId -> T.Type -> Bool
    compatibleType dbT hsT =
        case hsT of
            T.UnitT   -> True
            T.BoolT   -> L.elem dbT [H.SqlSmallIntT, H.SqlIntegerT, H.SqlBitT]
            T.StringT -> L.elem dbT [H.SqlCharT, H.SqlWCharT, H.SqlVarCharT]
            T.IntT    -> L.elem dbT [H.SqlSmallIntT, H.SqlIntegerT, H.SqlTinyIntT, H.SqlBigIntT, H.SqlNumericT]
            T.DoubleT -> L.elem dbT [H.SqlDecimalT, H.SqlRealT, H.SqlFloatT, H.SqlDoubleT]
            t         -> error $ printf "Unsupported column type %s for table %s" (show t) (show tableName)
