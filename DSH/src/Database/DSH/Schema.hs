-- | This module contains functionality to retrieve information about
-- the schema of actual database tables.
module Database.DSH.Schema
    ( getTableInfo
    , getX100TableInfo
    ) where

import qualified Data.List                as L
import           GHC.Exts
import           Text.Printf

import           Database.X100Client      hiding (X100, tableName)
import qualified Database.X100Client      as X

import qualified Database.DSH.Common.Type as T
import qualified Database.HDBC            as H

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
