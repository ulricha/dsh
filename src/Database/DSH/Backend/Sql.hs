{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE InstanceSigs      #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}

-- | This module implements the execution of SQL query bundles and the
-- construction of nested values from the resulting vector bundle.
module Database.DSH.Backend.Sql
  ( SqlBackend
  , sqlBackend
  ) where

import           Text.Printf

import qualified Database.HDBC                            as H
import           Database.HDBC.PostgreSQL

import           Control.Applicative
import           Control.Monad
import           Control.Monad.State
import qualified Data.Map                                 as M
import           Data.Maybe
import qualified Data.Text                                as Txt
import qualified Data.Text.Encoding                       as Txt
import           GHC.Exts

import qualified Database.Algebra.Dag                     as D
import qualified Database.Algebra.Dag.Build               as B
import           Database.Algebra.Dag.Common
import           Database.Algebra.SQL.Compatibility
import           Database.Algebra.SQL.Materialization.CTE
import           Database.Algebra.SQL.Util
import qualified Database.Algebra.Table.Lang              as TA

import           Database.DSH.Backend
import           Database.DSH.Backend.Sql.Opt.OptimizeTA
import           Database.DSH.Backend.Sql.VectorAlgebra   ()
import           Database.DSH.Common.QueryPlan
import qualified Database.DSH.Common.Type                 as T
import           Database.DSH.Frontend.Internals
import           Database.DSH.Impossible
import           Database.DSH.Translate.VL2Algebra
import qualified Database.DSH.VL.Lang                     as VL
import           Database.DSH.VL.Vector

--------------------------------------------------------------------------------

newtype SqlBackend = SqlBackend Connection

-- | Construct a PostgreSQL backend based on an HDBC PostgreSQL
-- connection.
sqlBackend :: Connection -> SqlBackend
sqlBackend = SqlBackend

--------------------------------------------------------------------------------

-- | In a query shape, render each root node for the algebraic plan
-- into a separate SQL query.

-- FIXME use materialization "prelude"
generateSqlQueries :: QueryPlan TA.TableAlgebra NDVec -> Shape (BackendCode SqlBackend)
generateSqlQueries taPlan = renderQueryCode $ queryShape taPlan
  where
    roots = D.rootNodes $ queryDag taPlan
    (_sqlShared, sqlQueries) = renderOutputDSHWith PostgreSQL materialize (queryDag taPlan)
    nodeToQuery  = zip roots sqlQueries
    lookupNode n = maybe $impossible SqlCode $ lookup n nodeToQuery

    renderQueryCode :: Shape NDVec -> Shape (BackendCode SqlBackend)
    renderQueryCode shape =
        case shape of
            SShape (ADVec r _) lyt -> SShape (lookupNode r) (convertLayout lyt)
            VShape (ADVec r _) lyt -> VShape (lookupNode r) (convertLayout lyt)

    convertLayout :: Layout NDVec -> Layout (BackendCode SqlBackend)
    convertLayout lyt =
        case lyt of
            LCol                   -> LCol
            LNest (ADVec r _) clyt -> LNest (lookupNode r) (convertLayout clyt)
            LTuple lyts            -> LTuple $ map convertLayout lyts

--------------------------------------------------------------------------------

-- | Insert SerializeRel operators in TA.TableAlgebra plans to define
-- descr and order columns as well as the required payload columns.
-- FIXME: once we are a bit more flexible wrt surrogates, determine the
-- surrogate (i.e. descr) columns from information in NDVec.
insertSerialize :: VecBuild TA.TableAlgebra NDVec (Shape NDVec)
                -> VecBuild TA.TableAlgebra NDVec (Shape NDVec)
insertSerialize g = g >>= traverseShape

  where
    traverseShape :: Shape NDVec -> VecBuild TA.TableAlgebra NDVec (Shape NDVec)
    traverseShape (VShape dvec lyt) = do
        mLyt' <- traverseLayout lyt
        case mLyt' of
            Just lyt' -> do
                dvec' <- insertOp dvec noDescr needAbsPos
                return $ VShape dvec' lyt'
            Nothing   -> do
                dvec' <- insertOp dvec noDescr needRelPos
                return $ VShape dvec' lyt

    traverseShape (SShape dvec lyt)     = do
        mLyt' <- traverseLayout lyt
        case mLyt' of
            Just lyt' -> do
                dvec' <- insertOp dvec noDescr needAbsPos
                return $ SShape dvec' lyt'
            Nothing   -> do
                dvec' <- insertOp dvec noDescr noPos
                return $ SShape dvec' lyt

    traverseLayout :: (Layout NDVec) -> VecBuild TA.TableAlgebra NDVec (Maybe (Layout NDVec))
    traverseLayout LCol          = return Nothing
    traverseLayout (LTuple lyts) = do
        mLyts <- mapM traverseLayout lyts
        if all isNothing mLyts
            then return Nothing
            else return $ Just $ LTuple $ zipWith (\l ml -> maybe l id ml) lyts mLyts
    traverseLayout (LNest dvec lyt) = do
        mLyt' <- traverseLayout lyt
        case mLyt' of
            Just lyt' -> do
                dvec' <- insertOp dvec needDescr needAbsPos
                return $ Just $ LNest dvec' lyt'
            Nothing   -> do
                dvec' <- insertOp dvec needDescr needRelPos
                return $ Just $ LNest dvec' lyt


    -- | Insert a Serialize node for the given vector
    insertOp :: NDVec -> Maybe TA.DescrCol -> TA.SerializeOrder -> VecBuild TA.TableAlgebra NDVec NDVec
    insertOp (ADVec q cols) descr pos = do
        let cs = map (TA.PayloadCol . ("item" ++) . show) cols
            op = TA.Serialize (descr, pos, cs)

        qp   <- lift $ B.insert $ UnOp op q
        return $ ADVec qp cols

    needDescr = Just (TA.DescrCol "descr")
    noDescr   = Nothing

    needAbsPos = TA.AbsPos "pos"
    needRelPos = TA.RelPos ["pos"]
    noPos      = TA.NoPos

implementVectorOps :: QueryPlan VL.VL VLDVec -> QueryPlan TA.TableAlgebra NDVec
implementVectorOps vlPlan = mkQueryPlan dag shape tagMap
  where
    taPlan               = vl2Algebra (D.nodeMap $ queryDag vlPlan) (queryShape vlPlan)
    serializedPlan       = insertSerialize taPlan
    (dag, shape, tagMap) = runVecBuild serializedPlan

--------------------------------------------------------------------------------
-- Utility functions for schema queries

-- | Translate an HDBC table description into the DSH schema format.
toTableDescr :: String -> [(String, H.SqlColDesc)] -> TableInfo
toTableDescr tableName cols = sortWith (\(n, _, _) -> n)
                    [ (name, show colTy, compatibleType tableName colTy)
                    | (name, props) <- cols
                    , let colTy = H.colType props
                    ]

-- | Determine if the DSH type and the attribute type in the backend
-- table are compatible.
compatibleType :: String -> H.SqlTypeId -> T.Type -> Bool
compatibleType tableName dbT hsT =
    case hsT of
        T.UnitT   -> True
        T.BoolT   -> elem dbT [H.SqlSmallIntT, H.SqlIntegerT, H.SqlBitT]
        T.StringT -> elem dbT [H.SqlCharT, H.SqlWCharT, H.SqlVarCharT]
        T.IntT    -> elem dbT [ H.SqlSmallIntT
                              , H.SqlIntegerT
                              , H.SqlTinyIntT
                              , H.SqlBigIntT
                              , H.SqlNumericT
                              ]
        T.DoubleT -> elem dbT [ H.SqlDecimalT
                              , H.SqlRealT
                              , H.SqlFloatT
                              , H.SqlDoubleT
                              ]
        t         -> error $ printf "Unsupported column type %s for table %s"
                                    (show t)
                                    (show tableName)

--------------------------------------------------------------------------------

instance Backend SqlBackend where
    data BackendRow SqlBackend  = SqlRow (M.Map String H.SqlValue)
    data BackendCode SqlBackend = SqlCode String
    data BackendPlan SqlBackend = QP (QueryPlan TA.TableAlgebra NDVec)

    execFlatQuery (SqlBackend conn) (SqlCode q) = do
        stmt  <- H.prepare conn q
        void $ H.execute stmt []
        map SqlRow <$> H.fetchAllRowsMap' stmt

    generateCode :: BackendPlan SqlBackend -> Shape (BackendCode SqlBackend)
    generateCode (QP plan) = generateSqlQueries plan

    generatePlan :: QueryPlan VL.VL VLDVec -> BackendPlan SqlBackend
    generatePlan = QP . implementVectorOps

    dumpPlan :: String -> BackendPlan SqlBackend -> IO ()
    dumpPlan prefix (QP plan) = do
        exportPlan (prefix ++ "_ta") plan
        exportPlan (prefix ++ "_opt_ta") $ optimizeTA plan

    querySchema (SqlBackend conn) tableName = do
        info <- H.describeTable conn tableName
        case info of
            []    -> error $ printf "Unknown table %s" tableName
            _ : _ -> return $ toTableDescr tableName info

--------------------------------------------------------------------------------

instance Row (BackendRow SqlBackend) where
    data Scalar (BackendRow SqlBackend) = SqlScalar H.SqlValue

    col c (SqlRow r) =
        case M.lookup c r of
            Just v  -> SqlScalar v
            Nothing -> error $ printf "col lookup %s failed in %s" c (show r)

    descrVal (SqlScalar (H.SqlInt32 i))   = fromIntegral i
    descrVal (SqlScalar (H.SqlInteger i)) = fromIntegral i
    descrVal _                          = $impossible

    scalarVal (SqlScalar H.SqlNull)           UnitT    = UnitE
    scalarVal (SqlScalar (H.SqlInteger _))    UnitT    = UnitE
    scalarVal (SqlScalar (H.SqlInteger i))    IntegerT = IntegerE i
    scalarVal (SqlScalar (H.SqlInt32 i))      IntegerT = IntegerE $ fromIntegral i
    scalarVal (SqlScalar (H.SqlInt64 i))      IntegerT = IntegerE $ fromIntegral i
    scalarVal (SqlScalar (H.SqlWord32 i))     IntegerT = IntegerE $ fromIntegral i
    scalarVal (SqlScalar (H.SqlWord64 i))     IntegerT = IntegerE $ fromIntegral i
    scalarVal (SqlScalar (H.SqlDouble d))     DoubleT  = DoubleE d
    scalarVal (SqlScalar (H.SqlRational d))   DoubleT  = DoubleE $ fromRational d
    scalarVal (SqlScalar (H.SqlInteger d))    DoubleT  = DoubleE $ fromIntegral d
    scalarVal (SqlScalar (H.SqlInt32 d))      DoubleT  = DoubleE $ fromIntegral d
    scalarVal (SqlScalar (H.SqlInt64 d))      DoubleT  = DoubleE $ fromIntegral d
    scalarVal (SqlScalar (H.SqlWord32 d))     DoubleT  = DoubleE $ fromIntegral d
    scalarVal (SqlScalar (H.SqlWord64 d))     DoubleT  = DoubleE $ fromIntegral d
    scalarVal (SqlScalar (H.SqlBool b))       BoolT    = BoolE b
    scalarVal (SqlScalar (H.SqlInteger i))    BoolT    = BoolE (i /= 0)
    scalarVal (SqlScalar (H.SqlInt32 i))      BoolT    = BoolE (i /= 0)
    scalarVal (SqlScalar (H.SqlInt64 i))      BoolT    = BoolE (i /= 0)
    scalarVal (SqlScalar (H.SqlWord32 i))     BoolT    = BoolE (i /= 0)
    scalarVal (SqlScalar (H.SqlWord64 i))     BoolT    = BoolE (i /= 0)
    scalarVal (SqlScalar (H.SqlChar c))       CharT    = CharE c
    scalarVal (SqlScalar (H.SqlString (c:_))) CharT    = CharE c
    scalarVal (SqlScalar (H.SqlByteString c)) CharT    = CharE (head $ Txt.unpack $ Txt.decodeUtf8 c)
    scalarVal (SqlScalar (H.SqlString t))     TextT    = TextE (Txt.pack t)
    scalarVal (SqlScalar (H.SqlByteString s)) TextT    = TextE (Txt.decodeUtf8 s)
    scalarVal (SqlScalar sql)               _        = error $ "Unsupported SqlValue: "  ++ show sql
