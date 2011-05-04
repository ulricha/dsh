{-# LANGUAGE GADTs, EmptyDataDecls, RankNTypes, FlexibleInstances, FlexibleContexts, TemplateHaskell #-}
module Language.ParallelLang.VL.Data.PlanBuilder where

import Database.Ferry.Algebra

import Language.ParallelLang.Common.Impossible

-- import Language.ParallelLang.Common.Data.Val

import Control.Applicative

type Graph b = forall a. GraphM (Plan a) b

-- | Results are stored in column:
pos, item1, descr, descr', descr'', pos', pos'', pos''', posold, posnew, ordCol, resCol, tmpCol, tmpCol' :: String
pos       = "pos"
item1     = "item1"
descr     = "iter"
descr'    = "item99999501"
descr''   = "item99999502"
pos'      = "item99999601"
pos''     = "item99999602"
pos'''    = "item99999603"
posold    = "item99999604"
posnew    = "item99999605"
ordCol    = "item99999801"
resCol    = "item99999001"
tmpCol    = "item99999002"
tmpCol'   = "item99999003"

class Prims a where
    
instance Prims Int where
    
data Plan a where
    PrimVal :: Prims a => AlgNode -> Plan a
    ValueVector :: Prims a => AlgNode -> Plan [a]
    NestedVector :: AlgNode -> Plan [a] -> Plan [[a]]
    TupleVector :: Plan a -> Plan b -> Plan (a, b)
    
data Descr where
    DescrVector :: AlgNode -> Descr

data Prop where
    PropVector :: AlgNode -> Prop

dist :: Plan a -> Plan [b] -> Graph (Plan [a])
dist q1@(PrimVal _) q2 = distPrim q1 q2
dist q1@(ValueVector _) q2 = undefined
    

distPrim :: Prims a => Plan a -> Plan [b] -> Graph (Plan [a])
distPrim v d = do
                 let (PrimVal q1) = v
                 (DescrVector q2) <- toDescr d
                 ValueVector <$> crossM (proj [(item1, item1)] q1) (return q2)
                 
attach :: Graph Descr -> Graph (Plan [a]) -> Graph (Plan [[a]])
attach d p = do
                (DescrVector q1) <- d
                NestedVector q1 <$> p
{-
distDesc :: Plan [a] -> Plan b -> Graph (Plan [a], Prop)
distDesc e1 e2 = do
                    (rf, q1, pf) <- determineResultVector e1
                    (DescrVector q2) <- toDescr e2
                    q <- projM (pf [(descr, pos), (pos, pos''), (posold, posold)]) $ rownumM pos'' [pos, pos'] Nothing $ crossM (proj [(pos, pos)] q2) (proj (pf [(pos', pos), (posold, pos)]) q1)
                    qr1 <- rf <$> proj (pf [(descr, descr), (pos, pos)]) q
                    qr2 <- PropVector <$> proj [(posold, posold), (posnew, pos)] q
                    return $ TupleVector [qr1, qr2]
-}
                 
toDescr :: Plan [a] -> Graph Descr
toDescr (NestedVector q _) = return $ DescrVector q
toDescr (ValueVector q)    = DescrVector <$> tagM "toDescr" (proj [(descr, descr), (pos, pos)] q)
toDescr (PrimVal _)        = $impossible

{-
    data Query a =
             TupleVector [Query a]
           | DescrVector a
           | ValueVector a
           | PrimVal a
           | NestedVector a (Query a)
           | PropVector a
    --       | UnEvaluated (Expr T.VType)
         deriving Show
-}
