module Language.ParallelLang.VL.VectorPrimitives where

import Database.Ferry.Algebra

import Control.Applicative
import Language.ParallelLang.VL.Algebra
import Language.ParallelLang.VL.Data.Query

-- * Vector primitive constructor functions

lengthA :: Plan -> Graph Plan
lengthA (DescrVector d) = PrimVal <$> (attachM descr natT (nat 1) $ attachM pos natT (nat 1) $ aggrM [(Max, "item1", Just "item1")] Nothing $ (litTable (int 0) "item1" intT) `unionM` (aggrM [(Count, "item1", Nothing)] Nothing $ proj [(pos, pos)] d))
lengthA (ValueVector d) = PrimVal <$> (attachM descr natT (nat 1) $ attachM pos natT (nat 1) $ aggrM [(Max, "item1", Just "item1")] Nothing $ (litTable (int 0) "item1" intT) `unionM` (aggrM [(Count, "item1", Nothing)] Nothing $ proj [(pos, pos)] d))

lengthSeg :: Plan -> Graph Plan
lengthSeg (ValueVector d) = ValueVector <$> (attachM pos natT (nat 1) $ aggrM [(Count, "item1", Nothing)] (Just descr) $ proj [(descr, descr)] d)
lengthSeg (DescrVector d) = ValueVector <$> (attachM pos natT (nat 1) $ aggrM [(Count, "item1", Nothing)] (Just descr) $ proj [(descr, descr)] d)

notA :: Plan -> Graph Plan
notA (PrimVal q1) = PrimVal <$> projM [(pos, pos), (descr, descr), (item1, resCol)] (notC resCol item1 q1)
notA (ValueVector q1) = ValueVector <$> projM [(pos, pos), (descr, descr), (item1, resCol)] (notC resCol item1 q1)

outer :: Plan -> Graph Plan
outer (NestedVector p _) = return $ DescrVector p
outer (ValueVector p)    = DescrVector <$> (tagM "outer" $ proj [(pos, pos), (descr,descr)] p)
outer e                  = error $ "outer: Can't extract outer plan" ++ show e
                
distPrim :: Plan -> Plan -> Graph Plan
distPrim (PrimVal q1) d = do
                 (DescrVector q2) <- toDescr d
                 ValueVector <$> crossM (proj [(item1, item1)] q1) (return q2)
                  
distDesc :: Plan -> Plan -> Graph Plan
distDesc e1 e2 = do
                   (rf, q1, pf) <- determineResultVector e1
                   (DescrVector q2) <- toDescr e2
                   q <- projM (pf [(descr, pos), (pos, pos''), (posold, posold)]) $ rownumM pos'' [pos, pos'] Nothing $ crossM (proj [(pos, pos)] q2) (proj (pf [(pos', pos), (posold, pos)]) q1)
                   qr1 <- rf <$> proj (pf [(descr, descr), (pos, pos)]) q
                   qr2 <- PropVector <$> proj [(posold, posold), (posnew, pos)] q
                   return $ TupleVector [qr1, qr2]

distLift :: Plan -> Plan -> Graph Plan
distLift e1 e2 = do
                    (rf, q1, pf) <- determineResultVector e1
                    (DescrVector q2) <- toDescr e2
                    q <- eqJoinM pos' descr (proj (pf [(pos', pos)]) q1) $ return q2
                    qr1 <- rf <$> proj (pf [(descr, descr), (pos, pos)]) q
                    qr2 <- DescrVector <$> proj [(posold, pos'), (posnew, pos)] q
                    return $ TupleVector [qr1, qr2]                    

rename :: Plan -> Plan -> Graph Plan
rename (PropVector q1) e2 = do
                (rf, q2, pf) <- determineResultVector e2
                q <- tagM "rename" $ projM (pf [(descr, posnew), (pos, pos)]) $ eqJoin posold descr q1 q2
                return $ rf q
                
propagateIn :: Plan -> Plan -> Graph Plan
propagateIn (PropVector q1) e2 = do
                     (rf, q2, pf) <- determineResultVector e2
                     q <- rownumM pos' [posnew, pos] Nothing $ eqJoin posold descr q1 q2
                     qr1 <- rf <$> proj (pf [(descr, posnew), (pos, pos')]) q
                     qr2 <- PropVector <$> proj [(posold, pos), (posnew, pos')] q
                     return $ TupleVector [qr1, qr2]
                     
attachV :: Plan -> Plan -> Plan
attachV (DescrVector q1) e2 = NestedVector q1 e2
                
singletonPrim :: Plan -> Graph Plan
singletonPrim (PrimVal q1) = do
                    return $ ValueVector q1
                    
singletonVec :: Plan -> Graph Plan
singletonVec e1 = do
                    q <- tagM "singletonVec" $ attachM pos natT (nat 1) $ litTable (nat 1) descr natT
                    return $ NestedVector q e1
                    
append :: Plan -> Plan -> Graph Plan
append e1 e2 = do
                (rf, q1, q2, pf) <- determineResultVector' e1 e2
                q <- rownumM pos' [descr, ordCol, pos] Nothing $ attach ordCol natT (nat 1) q1 `unionM` attach ordCol natT (nat 2) q2
                qv <- rf <$> tagM "append r" (proj (pf [(pos, pos'), (descr, descr)]) q)
                qp1 <- PropVector <$> (tagM "append r1" $ projM [(posold, pos), (posnew, pos')] $ selectM resCol $ operM "==" resCol ordCol tmpCol $ attach tmpCol natT (nat 1) q)
                qp2 <- PropVector <$> (tagM "append r2" $ projM [(posold, pos), (posnew, pos')] $ selectM resCol $ operM "==" resCol ordCol tmpCol $ attach tmpCol natT (nat 2) q)
                return $ TupleVector [qv, qp1, qp2]
                

segment :: Plan -> Graph Plan
segment e = do
             (rf, q, pf) <- determineResultVector e
             rf <$> proj (pf [(descr, pos), (pos, pos)]) q

extract :: Plan -> Int -> Graph Plan
extract p 0 = return p
extract (NestedVector _ p') n | n > 0 = extract p' (n - 1)
extract (AClosure n v l fvs x f1 f2) i | i < l = AClosure n <$> (extract v i) 
                                                             <*> pure (l - i) 
                                                             <*> (mapM (\(x, val) -> do
                                                                                        val' <- extract val i
                                                                                        return (x, val')) fvs)
                                                             <*> pure x <*> pure f1 <*> pure f2
extract v i = error $ "Extract: " ++ show v ++ " " ++ show i

insert :: Plan -> Plan -> Int -> Graph Plan
insert p _ 0 = return p
insert p d n | n > 0 = do
                        o <- outer d
                        d' <- extract d 1
                        insert (attachV o p) d' (n - 1)
             | otherwise = error "Can't insert a negative amount of descriptors"

restrictVec :: Plan -> Plan -> Graph Plan
restrictVec e1 (ValueVector qm) = do
                    (rf, q1, pf) <- determineResultVector e1
                    q <- rownumM pos'' [pos] Nothing $ selectM resCol $ eqJoinM pos pos' (return q1) $ proj [(pos', pos), (resCol, item1)] qm
                    qr <- rf <$> proj (pf [(pos, pos''), (descr, descr)]) q
                    qp <- PropVector <$> proj [(posold, pos), (posnew, pos'')] q
                    return $ TupleVector [qr, qp]

combineVec :: Plan -> Plan -> Plan -> Graph Plan
combineVec (ValueVector qb) e1 e2 = do
                        (rf, q1, q2, pf) <- determineResultVector' e1 e2
                        d1 <- projM [(pos', pos'), (pos, pos)] $ rownumM pos' [pos] Nothing $ select item1 qb
                        d2 <- projM [(pos', pos'), (pos, pos)] $ rownumM pos' [pos] Nothing $ selectM resCol $ notC resCol item1 qb
                        q <- eqJoinM pos' posold (return d1) (proj (pf [(posold, pos), (descr, descr)]) q1) `unionM` eqJoinM pos' posold (return d2) (proj (pf [(posold, pos), (descr, descr)]) q2)
                        qr <- rf <$> proj (pf [(descr, descr), (pos, pos)]) q
                        qp1 <- PropVector <$> proj [(posold, pos'), (posnew, pos)] d1
                        qp2 <- PropVector <$> proj [(posold, pos'), (posnew, pos)] d2
                        return $ TupleVector [qr, qp1, qp2]
                        
bPermuteVec :: Plan -> Plan -> Graph Plan
bPermuteVec e1 (ValueVector q2) = do
                     (rf, q1, pf) <- determineResultVector e1
                     q <- eqJoinM pos pos' (return q1) $ proj [(pos', pos), (posnew, item1)] q2
                     qr <- rf <$> proj (pf [(descr, descr), (pos, posnew)]) q
                     qp <- PropVector <$> proj [(posold, pos), (posnew, posnew)] q
                     return $ TupleVector [qr, qp]

determineResultVector :: Plan -> Graph (AlgNode -> Plan, AlgNode, ProjInf -> ProjInf)
determineResultVector e = do
                             let hasI = isValueVector e
                             let rf = if hasI then ValueVector else DescrVector
                             let pf = if hasI then \x -> (item1, item1):x else \x -> x
                             let q = if hasI
                                         then let (ValueVector q') = e in q'
                                         else let (DescrVector q') = e in q'
                             return (rf, q, pf)

determineResultVector' :: Plan -> Plan -> Graph (AlgNode -> Plan, AlgNode, AlgNode, ProjInf -> ProjInf)
determineResultVector' e1 e2 = do
                                 let hasI = isValueVector e1
                                 let rf = if hasI then ValueVector else DescrVector
                                 let pf = if hasI then \x -> (item1, item1):x else \x -> x
                                 let (q1, q2) = if hasI
                                                 then let (ValueVector q1') = e1
                                                          (ValueVector q2') = e2 in (q1', q2')
                                                 else let (DescrVector q1') = e1 
                                                          (DescrVector q2') = e2 in (q1', q2')
                                 return (rf, q1, q2, pf)
                                 
toDescr :: Plan -> Graph Plan
toDescr v@(DescrVector _) = return v
toDescr (ValueVector n)   = DescrVector <$> tagM "toDescr" (proj [(descr, descr), (pos, pos)] n)

isValueVector :: Plan -> Bool
isValueVector (ValueVector _) = True
isValueVector _               = False

tagVector :: String -> Plan -> Graph Plan
tagVector s (TupleVector vs) = TupleVector <$> (sequence $ map (\v -> tagVector s v) vs)
tagVector s (DescrVector q) = DescrVector <$> tag s q
tagVector s (ValueVector q) = ValueVector <$> tag s q
tagVector s (PrimVal q) = PrimVal <$> tag s q
tagVector s (NestedVector q qs) = NestedVector <$> tag s q <*> tagVector s qs
tagVector s (PropVector q) = PropVector <$> tag s q