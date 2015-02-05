{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE InstanceSigs      #-}
{-# LANGUAGE TemplateHaskell   #-}
{-# LANGUAGE TypeFamilies      #-}

-- | This module implements the execution of SQL query bundles and the
-- construction of nested values from the resulting vector bundle.
module Database.DSH.Backend.Sql
  ( SqlBackend(..)
  , BackendCode(..)
  ) where

import           Text.Printf

import           Database.HDBC
import           Database.HDBC.PostgreSQL

import           Control.Applicative
import           Control.Monad
import           Control.Monad.State
import qualified Data.Map                                 as M
import           Data.Maybe
import qualified Data.Text                                as Txt
import qualified Data.Text.Encoding                       as Txt

import qualified Database.Algebra.Dag                     as D
import qualified Database.Algebra.Dag.Build               as B
import           Database.Algebra.Dag.Common
import           Database.Algebra.SQL.Compatibility
import           Database.Algebra.SQL.Materialization.CTE
import           Database.Algebra.SQL.Util
import qualified Database.Algebra.Table.Lang              as TA

import           Database.DSH.Backend
import           Database.DSH.Backend.Sql.VectorAlgebra   ()
import           Database.DSH.Common.QueryPlan
import           Database.DSH.Frontend.Internals
import           Database.DSH.Impossible
import           Database.DSH.Translate.VL2Algebra
import qualified Database.DSH.VL.Lang                     as VL
import           Database.DSH.VL.Vector

newtype SqlBackend = SqlBackend Connection

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

implementVectorOpsPF :: QueryPlan VL.VL VLDVec -> QueryPlan TA.TableAlgebra NDVec
implementVectorOpsPF vlPlan = mkQueryPlan dag shape tagMap
  where
    taPlan               = vl2Algebra (D.nodeMap $ queryDag vlPlan) (queryShape vlPlan)
    serializedPlan       = insertSerialize taPlan
    (dag, shape, tagMap) = runVecBuild serializedPlan

--------------------------------------------------------------------------------

instance Backend SqlBackend where
    data BackendRow SqlBackend  = SqlRow (M.Map String SqlValue)
    data BackendCode SqlBackend = SqlCode String

    execFlatQuery (SqlBackend conn) (SqlCode q) = do
        stmt  <- prepare conn q
        void $ execute stmt []
        map SqlRow <$> fetchAllRowsMap' stmt

    generateCode :: QueryPlan VL.VL VLDVec -> Shape (BackendCode SqlBackend)
    generateCode = generateSqlQueries . implementVectorOpsPF

    querySchema = $unimplemented

--------------------------------------------------------------------------------

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
