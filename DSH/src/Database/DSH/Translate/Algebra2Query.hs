{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Translate.Algebra2Query (generateX100Query) where

import           Database.Algebra.Dag
import           Database.Algebra.Dag.Common
import           Database.Algebra.X100.Data
import           Database.Algebra.X100.Render

import           Database.DSH.Common.Data.QueryPlan hiding (mkQueryPlan)
import           Database.DSH.VL.Data.DBVector
import qualified Database.DSH.VL.Data.Query         as Q

generateX100Query :: QueryPlan X100Algebra -> Q.Query Q.X100
generateX100Query x100Plan = convertQuery $ queryShape x100Plan
 where
    m' :: NodeMap X100Algebra
    m' = nodeMap $ queryDag x100Plan

    convertQuery :: TopShape -> Q.Query Q.X100
    convertQuery (PrimVal (DBP r' _) l)     = Q.PrimVal (Q.X100 r' $ generateQuery m' r') $ convertLayout l
    convertQuery (ValueVector (DBV r' _) l) = Q.ValueVector (Q.X100 r' $ generateQuery m' r') $ convertLayout l

    convertLayout :: TopLayout -> Q.Layout Q.X100
    convertLayout (InColumn i)        = Q.InColumn i
    convertLayout (Nest (DBV r' _) l) = Q.Nest (Q.X100 r' $ generateQuery m' r') $ convertLayout l
    convertLayout (Pair p1 p2)        = Q.Pair (convertLayout p1) (convertLayout p2)
