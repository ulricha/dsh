{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Translate.Algebra2Query 
    ( generateSqlQueries
    ) where

import           Database.DSH.Impossible

import           Database.Algebra.Dag
import           Database.Algebra.Dag.Common
import           Database.Algebra.SQL.Compatibility
import           Database.Algebra.SQL.Materialization.CTE
import           Database.Algebra.SQL.Util
import           Database.Algebra.Table.Lang

import           Database.DSH.Common.DBCode
import           Database.DSH.Common.QueryPlan
import           Database.DSH.VL.Vector

-- | In a query shape, render each root node for the algebraic plan
-- into a separate SQL query.

-- FIXME use materialization "prelude"
generateSqlQueries :: QueryPlan TableAlgebra NDVec -> TopShape SqlCode
generateSqlQueries taPlan = renderQueryCode $ queryShape taPlan
  where
    roots = rootNodes $ queryDag taPlan
    (_sqlShared, sqlQueries) = renderOutputDSHWith PostgreSQL materialize (queryDag taPlan)
    nodeToQuery  = zip roots sqlQueries
    lookupNode n = maybe $impossible SqlCode $ lookup n nodeToQuery

    renderQueryCode :: TopShape NDVec -> TopShape SqlCode
    renderQueryCode shape =
        case shape of
            PrimVal (ADVec r _) lyt -> PrimVal (lookupNode r) (convertLayout lyt)
            ValueVector (ADVec r _) lyt -> ValueVector (lookupNode r) (convertLayout lyt)

    convertLayout :: TopLayout NDVec -> TopLayout SqlCode
    convertLayout lyt =
        case lyt of
            InColumn i            -> InColumn i
            Nest (ADVec r _) clyt -> Nest (lookupNode r) (convertLayout clyt)
            Pair lyt1 lyt2        -> Pair (convertLayout lyt1) (convertLayout lyt2)
