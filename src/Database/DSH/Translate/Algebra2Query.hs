{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Translate.Algebra2Query
    ( generateX100Queries
    , generateSqlQueries
    ) where

import           Database.DSH.Impossible

import           Database.Algebra.Dag
import           Database.Algebra.Dag.Common
import           Database.Algebra.SQL.Compatibility
import           Database.Algebra.SQL.Materialization.CTE
import           Database.Algebra.SQL.Util
import           Database.Algebra.Table.Lang
import           Database.Algebra.X100.Data
import           Database.Algebra.X100.Render

import           Database.DSH.Common.DBCode
import           Database.DSH.Common.QueryPlan
import           Database.DSH.VL.Vector

generateX100Queries :: QueryPlan X100Algebra NDVec -> Shape X100Code
generateX100Queries x100Plan = convertQuery $ queryShape x100Plan
 where
    m' :: NodeMap X100Algebra
    m' = nodeMap $ queryDag x100Plan

    convertQuery :: Shape NDVec -> Shape X100Code
    convertQuery (SShape (ADVec r' _) l) = SShape (X100Code $ generateQuery m' r') $ convertLayout l
    convertQuery (VShape (ADVec r' _) l) = VShape (X100Code $ generateQuery m' r') $ convertLayout l

    convertLayout :: Layout NDVec -> Layout X100Code
    convertLayout (LCol i)               = LCol i
    convertLayout (LNest (ADVec r' _) l) = LNest (X100Code $ generateQuery m' r') $ convertLayout l
    convertLayout (LPair p1 p2)          = LPair (convertLayout p1) (convertLayout p2)

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
