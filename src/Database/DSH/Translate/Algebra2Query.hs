{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Translate.Algebra2Query
    ( generateSqlQueries
    ) where

import           Database.DSH.Impossible

import           Database.Algebra.Dag
import           Database.Algebra.SQL.Compatibility
import           Database.Algebra.SQL.Materialization.CTE
import           Database.Algebra.SQL.Util
import           Database.Algebra.Table.Lang

import           Database.DSH.Common.QueryPlan
import           Database.DSH.Execute.Sql
import           Database.DSH.VL.Vector

-- | In a query shape, render each root node for the algebraic plan
-- into a separate SQL query.
generateSqlQueries :: QueryPlan TableAlgebra NDVec -> Shape (BackendCode SqlBackend)
generateSqlQueries taPlan = renderQueryCode $ queryShape taPlan
  where
    roots = rootNodes $ queryDag taPlan
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
            LCol i                 -> LCol i
            LNest (ADVec r _) clyt -> LNest (lookupNode r) (convertLayout clyt)
            LTuple lyts            -> LTuple $ map convertLayout lyts
