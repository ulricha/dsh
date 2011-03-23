module Language.ParallelLang.Translate.Vec2Algebra where

import Database.Ferry.Algebra hiding (getLoop, withContext, Gam)
import qualified Database.Ferry.Algebra as A

import Control.Applicative
type Graph = GraphM Plan


type Gam = A.Gam Plan

data Plan =
         Tuple [Plan]
       | DescrVector AlgNode
       | ValueVector AlgNode
       | PrimVal AlgNode
       | NestedVector AlgNode Plan
       | PropVector AlgNode
       
-- | Results are stored in column:
pos, item1, descr, descr', descr'', pos', pos'', pos''', posold, posnew, ordCol, resCol, tmpCol :: String
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


outer :: Graph Plan -> Graph Plan
outer e = do
            e' <- e
            case e' of
                NestedVector p _  -> return $ DescrVector p
                -- v@(ValueVector _) -> return $ v
                _                 -> error "outer: Can't extract outer plan"
                
distPrim :: Graph Plan -> Graph Plan -> Graph Plan
distPrim v d = do
                 (PrimVal q1) <- v
                 (DescrVector q2) <- toDescr d
                 DescrVector <$> crossM (proj [(item1, item1)] q1) (return q2)
                  
distDesc :: Graph Plan -> Graph Plan -> Graph Plan
distDesc e1 e2 = do
                   (rf, q1, pf) <- determineResultVector e1
                   (DescrVector q2) <- toDescr e2
                   q <- projM (pf [(descr, pos), (pos, pos''), (posold, posold)]) $ rownumM pos'' [pos, pos'] Nothing $ crossM (proj [(pos, pos)] q2) (proj (pf [(pos', pos), (posold, pos)]) q1)
                   qr1 <- rf <$> proj (pf [(descr, descr), (pos, pos)]) q
                   qr2 <- PropVector <$> proj [(posold, posold), (posnew, pos)] q
                   return $ Tuple [qr1, qr2]

distLift :: Graph Plan -> Graph Plan -> Graph Plan
distLift e1 e2 = do
                    (rf, q1, pf) <- determineResultVector e1
                    (DescrVector q2) <- toDescr e2
                    q <- eqJoinM pos' descr (proj (pf [(pos', pos)]) q1) $ return q2
                    qr1 <- rf <$> proj (pf [(descr, descr), (pos, pos)]) q
                    qr2 <- DescrVector <$> proj [(posold, pos'), (posnew, pos)] q
                    return $ Tuple [qr1, qr2]                    

rename :: Graph Plan -> Graph Plan -> Graph Plan
rename e1 e2 = do
                (PropVector q1) <- e1
                (rf, q2, pf) <- determineResultVector e2
                q <- projM (pf [(descr, posnew), (pos, pos)]) $ eqJoin posold descr q1 q2
                return $ rf q
                
propagateIn :: Graph Plan -> Graph Plan -> Graph Plan
propagateIn e1 e2 = do
                     (PropVector q1) <- e1
                     (rf, q2, pf) <- determineResultVector e2
                     q <- rownumM pos' [posnew, pos] Nothing $ eqJoin posold descr q1 q2
                     qr1 <- rf <$> proj (pf [(descr, posnew), (pos, pos')]) q
                     qr2 <- PropVector <$> proj [(posold, pos), (posnew, pos')] q
                     return $ Tuple [qr1, qr2]
                     
attachV :: Graph Plan -> Graph Plan -> Graph Plan
attachV e1 e2 = do
                 (DescrVector q1) <- e1
                 e2' <- e2
                 return $ NestedVector q1 e2'
                
singletonPrim :: Graph Plan -> Graph Plan
singletonPrim e1 = do
                    (PrimVal q1) <- e1
                    return $ ValueVector q1
                    
singletonVec :: Graph Plan -> Graph Plan
singletonVec e1 = do
                    e1' <- e1
                    q <- attachM pos natT (nat 1) $ litTable (nat 1) descr natT
                    return $ NestedVector q e1'
                    
append :: Graph Plan -> Graph Plan -> Graph Plan
append e1 e2 = do
                (rf, q1, q2, pf) <- determineResultVector' e1 e2
                q <- rownumM pos' [descr, ordCol, pos] Nothing $ attach ordCol natT (nat 1) q1 `unionM` attach ordCol natT (nat 2) q2
                qv <- rf <$> proj (pf [(pos, pos'), (descr, descr)]) q
                qp1 <- PropVector <$> (projM [(posold, pos), (posnew, pos')] $ selectM resCol $ operM "==" resCol ordCol tmpCol $ attach tmpCol natT (nat 1) q)
                qp2 <- PropVector <$> (projM [(posold, pos), (posnew, pos')] $ selectM resCol $ operM "==" resCol ordCol tmpCol $ attach tmpCol natT (nat 2) q)
                return $ Tuple [qv, qp1, qp2]
                

segment :: Graph Plan -> Graph Plan
segment e = do
             (rf, q, pf) <- determineResultVector e
             rf <$> proj (pf [(descr, pos), (pos, pos)]) q

extract :: Int -> Graph Plan -> Graph Plan
extract 0 p = p
extract n p | n > 0 = do
                       (NestedVector _ p') <- p
                       extract (n - 1) (return p')
            | otherwise = error "Can't extract a negative amount of descriptors"

insert :: Int -> Graph Plan -> Graph Plan -> Graph Plan
insert 0 p _ = p
insert n p d | n > 0 = insert (n - 1) (attachV (outer d) p) (extract 1 d)
             | otherwise = error "Can't insert a negative amount of descriptors"

restrictVec :: Graph Plan -> Graph Plan -> Graph Plan
restrictVec e1 m = do
                    (rf, q1, pf) <- determineResultVector e1
                    (ValueVector qm) <- m
                    q <- rownumM pos'' [pos] Nothing $ selectM resCol $ eqJoinM pos pos' (return q1) $ proj [(pos', pos), (resCol, item1)] qm
                    qr <- rf <$> proj (pf [(pos, pos''), (descr, descr)]) q
                    qp <- PropVector <$> proj [(posold, pos), (posnew, pos'')] q
                    return $ Tuple [qr, qp]

combineVec :: Graph Plan -> Graph Plan -> Graph Plan -> Graph Plan
combineVec eb e1 e2 = do
                        (rf, q1, q2, pf) <- determineResultVector' e1 e2
                        (ValueVector qb) <- eb
                        d1 <- projM [(pos', pos'), (pos, pos)] $ rownumM pos' [pos] Nothing $ select item1 qb
                        d2 <- projM [(pos', pos'), (pos, pos)] $ rownumM pos' [pos] Nothing $ selectM resCol $ notC resCol item1 qb
                        q <- eqJoinM pos' posold (return d1) (proj (pf [(posold, posold), (descr, descr)]) q1) `unionM` eqJoinM pos' posold (return d2) (proj (pf [(posold, posold), (descr, descr)]) q2)
                        qr <- rf <$> proj (pf [(descr, descr), (pos, pos)]) q
                        qp1 <- PropVector <$> proj [(posold, pos'), (posnew, pos)] d1
                        qp2 <- PropVector <$> proj [(posold, pos'), (posnew, pos)] d2
                        return $ Tuple [qr, qp1, qp2]
                        
bPermuteVec :: Graph Plan -> Graph Plan -> Graph Plan
bPermuteVec e1 e2 = do
                     (rf, q1, pf) <- determineResultVector e1
                     (ValueVector q2) <- e2
                     q <- eqJoinM pos pos' (return q1) $ proj [(pos', pos), (posnew, item1)] q2
                     qr <- rf <$> proj (pf [(descr, descr), (pos, posnew)]) q
                     qp <- PropVector <$> proj [(posold, pos), (posnew, posnew)] q
                     return $ Tuple [qr, qp]

determineResultVector :: Graph Plan -> Graph (AlgNode -> Plan, AlgNode, ProjInf -> ProjInf)
determineResultVector e = do
                            hasI <- isValueVector e
                            e' <- e
                            let rf = if hasI then ValueVector else DescrVector
                            let pf = if hasI then \x -> (item1, item1):x else \x -> x
                            let q = if hasI
                                        then let (ValueVector q') = e' in q'
                                        else let (DescrVector q') = e' in q'
                            return (rf, q, pf)

determineResultVector' :: Graph Plan -> Graph Plan -> Graph (AlgNode -> Plan, AlgNode, AlgNode, ProjInf -> ProjInf)
determineResultVector' e1 e2 = do
                                hasI <- isValueVector e1
                                e1' <- e1
                                e2' <- e2
                                let rf = if hasI then ValueVector else DescrVector
                                let pf = if hasI then \x -> (item1, item1):x else \x -> x
                                let (q1, q2) = if hasI
                                                then let (ValueVector q1') = e1'
                                                         (ValueVector q2') = e2' in (q1', q2')
                                                else let (DescrVector q1') = e1' 
                                                         (DescrVector q2') = e2' in (q1', q2')
                                return (rf, q1, q2, pf)

var :: String -> Graph Plan
var s = fromGam s


toDescr :: Graph Plan -> Graph Plan
toDescr v = do
             v' <- v
             case v' of
                 (DescrVector _) -> v
                 (ValueVector n) -> DescrVector <$> proj [(descr, descr), (pos, pos)] n
                                        
                 _               -> error "toDescr: Cannot cast into descriptor vector"

isValueVector :: Graph Plan -> Graph Bool
isValueVector p = do
                    p' <- p
                    case p' of
                        (ValueVector _) -> return True
                        _               -> return False