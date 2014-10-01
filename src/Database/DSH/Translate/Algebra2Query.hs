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
generateSqlQueries :: QueryPlan TableAlgebra NDVec -> Shape SqlCode
generateSqlQueries taPlan = renderQueryCode $ queryShape taPlan
  where
    roots = rootNodes $ queryDag taPlan
    (_sqlShared, sqlQueries) = renderOutputDSHWith PostgreSQL materialize (queryDag taPlan)
    nodeToQuery  = zip roots sqlQueries
    lookupNode n = maybe $impossible SqlCode $ lookup n nodeToQuery

    renderQueryCode :: Shape NDVec -> Shape SqlCode
    renderQueryCode shape =
        case shape of
            SShape (ADVec r _) lyt -> SShape (lookupNode r) (convertLayout lyt)
            VShape (ADVec r _) lyt -> VShape (lookupNode r) (convertLayout lyt)

    convertLayout :: Layout NDVec -> Layout SqlCode
    convertLayout lyt =
        case lyt of
            LCol i                 -> LCol i
            LNest (ADVec r _) clyt -> LNest (lookupNode r) (convertLayout clyt)
            LPair lyt1 lyt2        -> LPair (convertLayout lyt1) (convertLayout lyt2)
