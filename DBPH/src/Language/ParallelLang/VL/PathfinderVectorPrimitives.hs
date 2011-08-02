{-# LANGUAGE TemplateHaskell #-}
module Language.ParallelLang.VL.PathfinderVectorPrimitives where

import Control.Applicative hiding (Const)

import Language.ParallelLang.Common.Data.Val
import Language.ParallelLang.Common.Data.Op
import qualified Language.ParallelLang.Common.Data.Type as Ty
import Language.ParallelLang.NKL.Data.NKL
import qualified Language.ParallelLang.FKL.Data.FKL as FKL
import qualified Language.ParallelLang.VL.Data.VectorTypes as T
import Language.ParallelLang.VL.Data.Query
import Language.ParallelLang.VL.Algebra
import Language.ParallelLang.VL.VectorPrimitives

import Database.Algebra.Pathfinder
import Database.Algebra.Graph.GraphBuilder
import Database.Algebra.Impossible

instance VectorAlgebra PFAlgebra where
  groupBy = groupByPF
  notPrim = notPrimPF
  notVec = notVecPF
  lengthA = lengthAPF
  lengthSeg = lengthSegPF
  descToProp = descToPropPF
  notA = notAPF
  outer = outerPF
  distPrim = distPrimPF
  distDesc = distDescPF
  distLift = distLiftPF
  rename = renamePF
  propagateIn = propagateInPF
  singletonVec = singletonVecPF
  append = appendPF
  segment = segmentPF
  restrictVec = restrictVecPF
  combineVec = combineVecPF
  bPermuteVec = bPermuteVecPF
  constructLiteral = constructLiteralPF
  tableRef = tableRefPF
  binOp = binOpPF
  ifPrimValues = ifPrimPF
  ifValueVectors = ifValuePF
  initialLoop = initLoop
  tagVector = tagVectorPF
  emptyVector = emptyVectorPF

emptyVectorPF :: SchemaInfos -> Graph PFAlgebra AlgNode
emptyVectorPF infos = litTable' [] infos

ifPrimPF :: Plan -> Plan -> Plan -> Graph PFAlgebra Plan
ifPrimPF (PrimVal qc) (PrimVal qt) (PrimVal qe) = do
  qb <- proj [(tmpCol, item1)] qc
  qr <- projM [(descr, descr), (pos, pos), (item1, item1)] $ 
        selectM  tmpCol $ 
        unionM (cross qt qb) $ 
        crossM (return qe) $ 
        projM [(tmpCol, resCol)] $ notC resCol tmpCol qb
  return (PrimVal qr)
ifPrimPF _ _ _ = error "ifPrimPF: Can't translate if construction"

ifValuePF :: Plan -> Plan -> Plan -> Graph PFAlgebra Plan
ifValuePF (PrimVal qc) (PrimVal qt) (PrimVal qe) = do
  qb <- proj [(tmpCol, item1)] qc
  qr <- projM [(descr, descr), (pos, pos), (item1, item1)]
        $ selectM  tmpCol
        $ unionM (cross qt qb)
        $ crossM (return qe)
        $ projM [(tmpCol, resCol)] $ notC resCol tmpCol qb
  return (ValueVector qr)
ifValuePF _ _ _ = error "ifValuePF: Can't translate if construction"

applyBinOp :: Oper -> AlgNode -> AlgNode -> Graph PFAlgebra AlgNode
applyBinOp op q1 q2 =
  projM [(item1, resCol), (descr, descr), (pos, pos)] 
    $ operM (show op) resCol item1 tmpCol 
    $ eqJoinM pos pos' (return q1) 
    $ proj [(tmpCol, item1), (pos', pos)] q2

binOpPF :: Bool -> Oper -> Plan -> Plan -> Graph PFAlgebra Plan
binOpPF True op (ValueVector q1) (ValueVector q2) = do 
  q <- applyBinOp op q1 q2
  return (ValueVector q)
binOpPF False op (PrimVal q1) (PrimVal q2) = do
  q <- applyBinOp op q1 q2
  return (PrimVal q)
binOpPF _ _ _ _ = $impossible

groupByPF :: Plan -> Plan -> Graph PFAlgebra Plan
groupByPF (ValueVector v1) (ValueVector v2) = do
                                             q' <- rownumM pos' [resCol, pos] Nothing $ rowrank resCol [(descr, Asc), (item1, Asc)] v1
                                             d1 <- distinctM $ proj [(descr, descr), (pos, resCol)] q'
                                             p <- proj [(posold, pos), (posnew, pos')] q'
                                             v <- tagM "groupBy ValueVector" $ projM [(descr, descr), (pos, pos), (item1, item1)]
                                                    $ eqJoinM pos'' pos' (proj [(descr, resCol), (pos, pos'), (pos'', pos)] q')
                                                                         (proj [(pos', pos), (item1, item1)] v2)
                                             return $ TupleVector [DescrVector d1, ValueVector v, PropVector p]
groupByPF (ValueVector v1) (DescrVector v2) = do
                                             q' <- rownumM pos' [resCol, pos] Nothing $ rowrank resCol [(descr, Asc), (item1, Asc)] v1
                                             d1 <- distinctM $ proj [(descr, descr), (pos, resCol)] q'
                                             p <- proj [(posold, pos), (posnew, pos')] q'
                                             v <- projM [(descr, descr), (pos, pos), (item1, item1)]
                                                    $ eqJoinM pos'' pos' (proj [(descr, resCol), (pos, pos'), (pos'', pos)] q')
                                                                         (proj [(pos', pos)] v2)
                                             return $ TupleVector [DescrVector d1, DescrVector v, PropVector p]
groupByPF _ _ = error "groupBy: Should not be possible"

notPrimPF :: Plan -> Graph PFAlgebra Plan
notPrimPF (PrimVal q) = PrimVal <$> (projM [(pos, pos), (descr, descr), (item1, tmpCol)] $ notC tmpCol item1 q)
notPrimPF _ = error "notPrimPF: Should not be possible"

notVecPF :: Plan -> Graph PFAlgebra Plan
notVecPF (ValueVector d) = ValueVector <$> (projM [(pos, pos), (descr, descr), (item1, tmpCol)] $ notC tmpCol item1 d)
notVecPF _ = error "notVecPF: Should not be possible"

lengthAPF :: Plan -> Graph PFAlgebra Plan
lengthAPF (DescrVector d) = PrimVal <$> (attachM descr natT (nat 1) $ attachM pos natT (nat 1) $ aggrM [(Max, "item1", Just "item1")] Nothing $ (litTable (int 0) "item1" intT) `unionM` (aggrM [(Count, "item1", Nothing)] Nothing $ proj [(pos, pos)] d))
lengthAPF (ValueVector d) = PrimVal <$> (attachM descr natT (nat 1) $ attachM pos natT (nat 1) $ aggrM [(Max, "item1", Just "item1")] Nothing $ (litTable (int 0) "item1" intT) `unionM` (aggrM [(Count, "item1", Nothing)] Nothing $ proj [(pos, pos)] d))
lengthAPF _ = error "lengthAPF: Should not be possible"

lengthSegPF :: Plan -> Plan -> Graph PFAlgebra Plan
lengthSegPF (DescrVector q1) (ValueVector d) = ValueVector <$> (rownumM pos [descr] Nothing $ aggrM [(Max, "item1", Just "item1")] (Just descr) $ (attachM "item1" intT (int 0) $ proj [(descr, pos)] q1) `unionM` (aggrM [(Count, "item1", Nothing)] (Just descr) $ proj [(descr, descr)] d))
lengthSegPF (DescrVector q1) (DescrVector d) = ValueVector <$> (rownumM pos [descr] Nothing $ aggrM [(Max, "item1", Just "item1")] (Just descr) $ (attachM "item1" intT (int 0) $ proj [(descr, pos)] q1) `unionM` (aggrM [(Count, "item1", Nothing)] (Just descr) $ proj [(descr, descr)] d))
lengthSegPF _ _ = error "lengthSegPF: Should not be possible"

descToPropPF :: Plan -> Graph PFAlgebra Plan
descToPropPF (DescrVector q1) = PropVector <$> proj [(posnew, descr), (posold, pos)] q1
descToPropPF _ = error "descToPropPF: Should not be possible"

notAPF :: Plan -> Graph PFAlgebra Plan
notAPF (PrimVal q1) = PrimVal <$> projM [(pos, pos), (descr, descr), (item1, resCol)] (notC resCol item1 q1)
notAPF (ValueVector q1) = ValueVector <$> projM [(pos, pos), (descr, descr), (item1, resCol)] (notC resCol item1 q1)
notAPF _ = error "notAPF: Should not be possible"

outerPF :: Plan -> Graph PFAlgebra Plan
outerPF (NestedVector p _) = return $ DescrVector p
outerPF (ValueVector p)    = DescrVector <$> (tagM "outerPF" $ proj [(pos, pos), (descr,descr)] p)
outerPF e                  = error $ "outerPF: Can't extract outerPF plan" ++ show e
                
distPrimPF :: Plan -> Plan -> Graph PFAlgebra Plan
distPrimPF (PrimVal q1) d = do
                 (DescrVector q2) <- toDescr d
                 ValueVector <$> crossM (proj [(item1, item1)] q1) (return q2)
distPrimPF _ _ = error "distPrimPF: Should not be possible"
                  
distDescPF :: Plan -> Plan -> Graph PFAlgebra Plan
distDescPF e1 e2 = do
                   (rf, q1, pf) <- determineResultVector e1
                   (DescrVector q2) <- toDescr e2
                   q <- projM (pf [(descr, pos), (pos, pos''), (posold, posold)]) $ rownumM pos'' [pos, pos'] Nothing $ crossM (proj [(pos, pos)] q2) (proj (pf [(pos', pos), (posold, pos)]) q1)
                   qr1 <- rf <$> proj (pf [(descr, descr), (pos, pos)]) q
                   qr2 <- PropVector <$> proj [(posold, posold), (posnew, pos)] q
                   return $ TupleVector [qr1, qr2]

distLiftPF :: Plan -> Plan -> Graph PFAlgebra Plan
distLiftPF e1 e2 = do
                    (rf, q1, pf) <- determineResultVector e1
                    (DescrVector q2) <- toDescr e2
                    q <- eqJoinM pos' descr (proj (pf [(pos', pos)]) q1) $ return q2
                    qr1 <- rf <$> proj (pf [(descr, descr), (pos, pos)]) q
                    qr2 <- DescrVector <$> proj [(posold, pos'), (posnew, pos)] q
                    return $ TupleVector [qr1, qr2]                    

renamePF :: Plan -> Plan -> Graph PFAlgebra Plan
renamePF (PropVector q1) e2 = do
                (rf, q2, pf) <- determineResultVector e2
                q <- tagM "renamePF" $ projM (pf [(descr, posnew), (pos, pos)]) $ eqJoin posold descr q1 q2
                return $ rf q
renamePF _ _ = error "renamePF: Should not be possible"
                
propagateInPF :: Plan -> Plan -> Graph PFAlgebra Plan
propagateInPF (PropVector q1) e2 = do
                     (rf, q2, pf) <- determineResultVector e2
                     q <- rownumM pos' [posnew, pos] Nothing $ eqJoin posold descr q1 q2
                     qr1 <- rf <$> proj (pf [(descr, posnew), (pos, pos')]) q
                     qr2 <- PropVector <$> proj [(posold, pos), (posnew, pos')] q
                     return $ TupleVector [qr1, qr2]
propagateInPF _ _ = error "propagateInPF: Should not be possible"
                     
singletonVecPF :: Plan -> Graph PFAlgebra Plan
singletonVecPF e1 = do
                    q <- tagM "singletonVecPF" $ attachM pos natT (nat 1) $ litTable (nat 1) descr natT
                    return $ NestedVector q e1
                    
appendPF :: Plan -> Plan -> Graph PFAlgebra Plan
appendPF e1 e2 = do
                (rf, q1, q2, pf) <- determineResultVector' e1 e2
                q <- rownumM pos' [descr, ordCol, pos] Nothing $ attach ordCol natT (nat 1) q1 `unionM` attach ordCol natT (nat 2) q2
                qv <- rf <$> tagM "append r" (proj (pf [(pos, pos'), (descr, descr)]) q)
                qp1 <- PropVector <$> (tagM "append r1" $ projM [(posold, pos), (posnew, pos')] $ selectM resCol $ operM "==" resCol ordCol tmpCol $ attach tmpCol natT (nat 1) q)
                qp2 <- PropVector <$> (tagM "append r2" $ projM [(posold, pos), (posnew, pos')] $ selectM resCol $ operM "==" resCol ordCol tmpCol $ attach tmpCol natT (nat 2) q)
                return $ TupleVector [qv, qp1, qp2]
                

segmentPF :: Plan -> Graph PFAlgebra Plan
segmentPF e = do
             (rf, q, pf) <- determineResultVector e
             rf <$> proj (pf [(descr, pos), (pos, pos)]) q


restrictVecPF :: Plan -> Plan -> Graph PFAlgebra Plan
restrictVecPF e1 (ValueVector qm) = do
                    (rf, q1, pf) <- determineResultVector e1
                    q <- rownumM pos'' [pos] Nothing $ selectM resCol $ eqJoinM pos pos' (return q1) $ proj [(pos', pos), (resCol, item1)] qm
                    qr <- rf <$> proj (pf [(pos, pos''), (descr, descr)]) q
                    qp <- PropVector <$> proj [(posold, pos), (posnew, pos'')] q
                    return $ TupleVector [qr, qp]
restrictVecPF _ _ = error "restrictVecPF: Should not be possible"

combineVecPF :: Plan -> Plan -> Plan -> Graph PFAlgebra Plan
combineVecPF (ValueVector qb) e1 e2 = do
                        (rf, q1, q2, pf) <- determineResultVector' e1 e2
                        d1 <- projM [(pos', pos'), (pos, pos)] $ rownumM pos' [pos] Nothing $ select item1 qb
                        d2 <- projM [(pos', pos'), (pos, pos)] $ rownumM pos' [pos] Nothing $ selectM resCol $ notC resCol item1 qb
                        q <- eqJoinM pos' posold (return d1) (proj (pf [(posold, pos), (descr, descr)]) q1) `unionM` eqJoinM pos' posold (return d2) (proj (pf [(posold, pos), (descr, descr)]) q2)
                        qr <- rf <$> proj (pf [(descr, descr), (pos, pos)]) q
                        qp1 <- PropVector <$> proj [(posold, pos'), (posnew, pos)] d1
                        qp2 <- PropVector <$> proj [(posold, pos'), (posnew, pos)] d2
                        return $ TupleVector [qr, qp1, qp2]
combineVecPF _ _ _ = error "combineVecPF: Should not be possible"
                        
bPermuteVecPF :: Plan -> Plan -> Graph PFAlgebra Plan
bPermuteVecPF e1 (ValueVector q2) = do
                     (rf, q1, pf) <- determineResultVector e1
                     q <- eqJoinM pos pos' (return q1) $ proj [(pos', pos), (posnew, item1)] q2
                     qr <- rf <$> proj (pf [(descr, descr), (pos, posnew)]) q
                     qp <- PropVector <$> proj [(posold, pos), (posnew, posnew)] q
                     return $ TupleVector [qr, qp]
bPermuteVecPF _ _ = error "bpermuteVecPF: Should not be possible"

-- constructLiteralPF :: VectorAlgebra a => Ty.Type -> Val -> Graph a Plan
constructLiteralPF :: Ty.Type -> Val -> Graph PFAlgebra Plan
constructLiteralPF t (List es) = listToPlan t (zip (repeat 1) es)
constructLiteralPF _t v = PrimVal <$> (tagM "constant" $ (attachM descr natT (nat 1) $ attachM pos natT (nat 1) $ constructLiteralPF' v))
 where
  constructLiteralPF' (Int i) = litTable (int $ fromIntegral i) item1 intT
  constructLiteralPF' (Bool b) = litTable (bool b) item1 boolT
  constructLiteralPF' Unit     = litTable (int (-1)) item1 intT  
  constructLiteralPF' (String s) = litTable (string s) item1 stringT
  constructLiteralPF' (Double d) = litTable (double d) item1 doubleT
  constructLiteralPF' (List _) = $impossible 

-- listToPlan :: VectorAlgebra a => Typ.Type -> [(Integer, Val)] -> Graph a Plan
listToPlan :: Ty.Type -> [(Integer, Val)] -> Graph PFAlgebra Plan
listToPlan (Ty.List t@(Ty.List _)) [] = do
                                               d <- emptyTable [("iter", natT), ("pos", natT)]
                                               v <- listToPlan t []
                                               return $ NestedVector d v
listToPlan (Ty.List t@(Ty.List _)) vs = do
                                          let (vals, rec) = unzip [([nat i, nat p], zip (repeat p) es) | (p, (i, List es)) <- zip [1..] vs]
                                          d <- litTable' vals  [("iter", natT), ("pos", natT)]
                                          v <- listToPlan t $ concat rec
                                          return $ NestedVector d v                                                    
listToPlan (Ty.List t) [] = ValueVector <$> emptyTable [("iter", natT), ("pos", natT), ("item1", algTy t)]
listToPlan (Ty.List t) vs = ValueVector <$> litTable' [[nat i, nat p, toAlgVal v] | (p, (i, v)) <- zip [1..] vs] [("iter", natT), ("pos", natT), ("item1", algTy t)]
listToPlan _ _ = $impossible "Not a list value or type"
       
algTy :: Ty.Type -> ATy
algTy (Ty.Int) = intT
algTy (Ty.Double) = doubleT
algTy (Ty.Bool) = boolT
algTy (Ty.String) = stringT
algTy (Ty.Unit) = intT
algTy _               = $impossible "Not a primitive type"

toAlgVal :: Val -> AVal
toAlgVal (Int i) = int $ fromIntegral i
toAlgVal (Bool b) = bool b
toAlgVal Unit = int (-1)
toAlgVal (String s) = string s
toAlgVal (Double d) = double d
toAlgVal _ = $impossible "Not a primitive value"

-- | Construct a name that represents a lifted variable in the environment.                        
constrEnvName :: String -> Int -> String
constrEnvName x 0 = x
constrEnvName x i = x ++ "<%>" ++ show i

tableRefPF :: String -> [FKL.Column Ty.Type] -> KeyInfos -> Graph PFAlgebra Plan
tableRefPF n cs ks = do
                     table <- dbTable n (renameCols cs) ks
                     t' <- attachM descr natT (nat 1) $ rownum pos (head ks) Nothing table
                     cs' <- mapM (\(_, i) -> ValueVector <$> proj [(descr, descr), (pos, pos), (item1, "item" ++ show i)] t') $ zip cs [1..]
                     return $ foldl1 (\x y -> TupleVector [y,x]) $ reverse cs'
  where
    renameCols :: [FKL.Column Ty.Type] -> [Column]
    renameCols xs = [NCol cn [Col i $ algTy t]| ((cn, t), i) <- zip xs [1..]]

determineResultVector :: Plan -> Graph PFAlgebra (AlgNode -> Plan, AlgNode, ProjInf -> ProjInf)
determineResultVector e = do
                             let hasI = isValueVector e
                             let rf = if hasI then ValueVector else DescrVector
                             let pf = if hasI then \x -> (item1, item1):x else \x -> x
                             let q = if hasI
                                         then let (ValueVector q') = e in q'
                                         else let (DescrVector q') = e in q'
                             return (rf, q, pf)

determineResultVector' :: Plan -> Plan -> Graph PFAlgebra (AlgNode -> Plan, AlgNode, AlgNode, ProjInf -> ProjInf)
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
                                 
toDescr :: Plan -> Graph PFAlgebra Plan
toDescr v@(DescrVector _) = return v
toDescr (ValueVector n)   = DescrVector <$> tagM "toDescr" (proj [(descr, descr), (pos, pos)] n)
toDescr _ = error "toDescr: Should not be possible"

tagVectorPF :: String -> Plan -> Graph PFAlgebra Plan
tagVectorPF s (TupleVector vs) = TupleVector <$> (sequence $ map (\v -> tagVectorPF s v) vs)
tagVectorPF s (DescrVector q) = DescrVector <$> tag s q
tagVectorPF s (ValueVector q) = ValueVector <$> tag s q
tagVectorPF s (PrimVal q) = PrimVal <$> tag s q
tagVectorPF s (NestedVector q qs) = NestedVector <$> tag s q <*> tagVectorPF s qs
tagVectorPF s (PropVector q) = PropVector <$> tag s q
tagVectorPF _ _ = error "tagVectorPF: Should not be possible"
