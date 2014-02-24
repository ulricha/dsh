{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Translate.Algebra2Query 
    ( generateX100Query
    , generateSqlQueries
    ) where

import Database.DSH.Impossible

import Database.Algebra.Dag
import Database.Algebra.Dag.Common
import Database.Algebra.X100.Data
import Database.Algebra.X100.Render
import Database.Algebra.Pathfinder
import Database.Algebra.SQL.Util
import Database.Algebra.SQL.Compatibility

import Database.DSH.Common.Data.QueryPlan hiding (mkQueryPlan)
import Database.DSH.VL.Data.DBVector
import Database.DSH.Common.Data.DBCode

generateX100Query :: QueryPlan X100Algebra -> TopShape X100Code
generateX100Query x100Plan = convertQuery $ queryShape x100Plan
 where
    m' :: NodeMap X100Algebra
    m' = nodeMap $ queryDag x100Plan

    convertQuery :: TopShape DVec -> TopShape X100Code
    convertQuery (PrimVal (DVec r' _) l)     = PrimVal (X100Code r' $ generateQuery m' r') $ convertLayout l
    convertQuery (ValueVector (DVec r' _) l) = ValueVector (X100Code r' $ generateQuery m' r') $ convertLayout l

    convertLayout :: TopLayout DVec -> TopLayout X100Code
    convertLayout (InColumn i)         = InColumn i
    convertLayout (Nest (DVec r' _) l) = Nest (X100Code r' $ generateQuery m' r') $ convertLayout l
    convertLayout (Pair p1 p2)         = Pair (convertLayout p1) (convertLayout p2)

-- | In a query shape, render each root node for the algebraic plan
-- into a separate SQL query.

-- FIXME use materialization "prelude"
generateSqlQueries :: QueryPlan PFAlgebra -> TopShape SqlCode
generateSqlQueries taPlan = renderQueryCode $ queryShape taPlan
  where
    roots = rootNodes $ queryDag taPlan
    (_sqlShared, sqlQueries) = renderOutputDSHWith PostgreSQL $unimplemented (queryDag taPlan)
    nodeToQuery  = zip roots sqlQueries
    lookupNode n = maybe $impossible SqlCode $ lookup n nodeToQuery

    renderQueryCode :: TopShape DVec -> TopShape SqlCode
    renderQueryCode shape =
        case shape of
            PrimVal (DVec r _) lyt -> PrimVal (lookupNode r) (convertLayout lyt)
            ValueVector (DVec r _) lyt -> ValueVector (lookupNode r) (convertLayout lyt)

    convertLayout :: TopLayout DVec -> TopLayout SqlCode
    convertLayout lyt =
        case lyt of
            InColumn i           -> InColumn i
            Nest (DVec r _) clyt -> Nest (lookupNode r) (convertLayout clyt)
            Pair lyt1 lyt2       -> Pair (convertLayout lyt1) (convertLayout lyt2)
