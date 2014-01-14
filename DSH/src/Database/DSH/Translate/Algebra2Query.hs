{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Translate.Algebra2Query (generateX100Query) where

import Database.Algebra.Dag
import Database.Algebra.Dag.Common
import Database.Algebra.X100.Data
import Database.Algebra.X100.Render

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
