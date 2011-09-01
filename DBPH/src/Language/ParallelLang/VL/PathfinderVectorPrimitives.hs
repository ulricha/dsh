{-# LANGUAGE TemplateHaskell #-}
module Language.ParallelLang.VL.PathfinderVectorPrimitives where

import Data.Maybe

import Control.Applicative hiding (Const)

import Language.ParallelLang.Common.Impossible
import Language.ParallelLang.Common.Data.Val
import Language.ParallelLang.Common.Data.Op
import qualified Language.ParallelLang.Common.Data.Type as Ty
import qualified Language.ParallelLang.FKL.Data.FKL as FKL
import Language.ParallelLang.VL.Data.Query
import Language.ParallelLang.VL.Algebra
import Language.ParallelLang.VL.VectorPrimitives
import Language.ParallelLang.VL.MetaPrimitives

import Database.Algebra.Pathfinder
import Database.Algebra.Graph.Common
import Database.Algebra.Graph.GraphBuilder

instance VectorAlgebra PFAlgebra where
  groupBy = groupByPF
  notA = notAPF
  notPrim = notPrimPF
  notVec = notVecPF
  lengthA = lengthAPF
  lengthSeg = lengthSegPF
  descToProp = descToPropPF
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
  emptyVector = emptyVectorPF
  ifPrimList = ifPrimListPF
  ifNestList = isNestListM
  sortWith = sortWithPF
  vecSum = vecSumPF
  vecSumLift = vecSumLiftPF
  selectPos = selectPosPF
  selectPosLift = selectPosLiftPF
  -- FIXME implement empty primitives
  empty = undefined
  emptyLift = undefined

-- | Results are stored in column:
pos, item', item, descr, descr', descr'', pos', pos'', pos''', posold, posnew, ordCol, resCol, tmpCol, tmpCol' :: AttrName
pos       = "pos"
item      = "item1"
item'     = "item2"
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

algCol :: AbstractColumn -> AttrName
algCol (AuxCol c) = auxCol c
algCol (DataCol s) = s

{-
concretizeProjInfo :: AbstractProjInfo -> ProjInf
concretizeProjInfo = map (\(c1, c2) -> (algCol c1, algCol c2))
-}

auxCol :: AuxColumn -> AttrName
auxCol Pos = pos
auxCol Pos' = pos'
auxCol Pos'' = pos''
auxCol Pos''' = pos'''
auxCol Descr = descr
auxCol Descr' = descr'
auxCol Descr'' = descr'
auxCol PosOld = posold
auxCol PosNew = posnew
auxCol OrdCol = ordCol
auxCol ResCol = resCol
auxCol TmpCol = tmpCol
auxCol TmpCol' = tmpCol'
auxCol Item = item
auxCol Item' = item'

emptyVectorPF :: [TypedAbstractColumn Ty.Type] -> Graph PFAlgebra AlgNode
emptyVectorPF infos = emptyTable $ map (\(x,y) -> (algCol x, algTy y)) infos

selectPosLiftPF :: Plan -> Oper -> Plan -> Graph PFAlgebra Plan
selectPosLiftPF e op (ValueVector qi) =
    do
        (rf, qe, pf) <- determineResultVector e
        qs <- rownumM posnew [descr, pos] Nothing
              $ selectM resCol
              $ operM (show op) resCol pos' item'
              $ eqJoinM descr pos''
              (rownum pos' [pos] (Just descr) qe)
              (proj [(pos'', pos), (item', item)] qi)
        q <- proj (pf [(descr, descr), (pos, posnew)]) qs
        qp <- proj [(posold, pos), (posnew, posnew)] qs
        return $ TupleVector [rf q, PropVector qp]

selectPosPF :: Plan -> Oper -> Plan -> Graph PFAlgebra Plan
selectPosPF e op (PrimVal qi) =
    do
        (rf, qe, pf) <- determineResultVector e
        qs <- selectM resCol
              $ operM (show op) resCol pos' item'
              $ crossM
              (proj (pf [(descr, descr), (pos', pos)]) qe)
              (proj [(item', item)] qi)
        qn <- case op of 
                Lt -> 
                    proj (pf [(descr, descr), (pos, pos'), (pos', pos')]) qs 
                LtE -> 
                    proj (pf [(descr, descr), (pos, pos'), (pos', pos')]) qs 
                _ -> 
                    projM (pf [(descr, descr), (pos, pos), (pos', pos')])
                    $ rownum pos [descr, pos'] Nothing qs
        q <- proj (pf [(descr, descr), (pos, pos)]) qn
        qp <- proj [(posnew, pos), (posold, pos')] qn
        return $ TupleVector [rf q, PropVector qp]

vecSumPF :: Plan -> Graph PFAlgebra Plan
vecSumPF (ValueVector q) =
    do
        qs <- attachM descr natT (nat 1)
             $ attachM pos natT (nat 1)
             $ aggr [(Sum, item, Just item)] Nothing q
        return $ PrimVal qs
vecSumPF _ = $impossible

vecSumLiftPF :: Plan -> Plan -> Graph PFAlgebra Plan
vecSumLiftPF (DescrVector qd) (ValueVector qv) =
    do
        qe <- attachM item intT (int 0)
              $ attachM pos natT (nat 1)
              $ differenceM
                (proj [(descr, pos)] qd)
                (proj [(descr, descr)] qv)
        qs <- attachM pos natT (nat 1)
              $ aggr [(Sum, item, Just item)] (Just descr) qv
        qr <- union qe qs
        return $ ValueVector qr
vecSumLiftPF _ _ = $impossible

applyBinOp :: Oper -> AlgNode -> AlgNode -> Graph PFAlgebra AlgNode
applyBinOp op q1 q2 =
  projM [(item, resCol), (descr, descr), (pos, pos)] 
    $ operM (show op) resCol item tmpCol 
    $ eqJoinM pos pos' (return q1) 
    $ proj [(tmpCol, item), (pos', pos)] q2

binOpPF :: Bool -> Oper -> Plan -> Plan -> Graph PFAlgebra Plan
binOpPF True op (ValueVector q1) (ValueVector q2) = do 
  q <- applyBinOp op q1 q2
  return (ValueVector q)
binOpPF False op (PrimVal q1) (PrimVal q2) = do
  q <- applyBinOp op q1 q2
  return (PrimVal q)
binOpPF _ _ _ _ = $impossible

sortWithPF :: Plan -> Plan -> Graph PFAlgebra Plan
sortWithPF (ValueVector qs) e = 
    do
        (rf, qe, pf) <- determineResultVector e
        q <- tagM "sortWith" 
             $ eqJoinM pos pos''
               (projM [(pos, pos), (pos', pos')]
                $ rownum pos' [descr, item] Nothing qs)
               (proj (pf [(descr, descr), (pos'', pos)]) qe)
        qv <- proj (pf [(descr, descr), (pos, pos')]) q
        qp <- proj [(posold, pos''), (posnew, pos')] q
        return $ TupleVector [rf qv, PropVector qp]

groupByPF :: Plan -> Plan -> Graph PFAlgebra Plan
groupByPF (ValueVector v1) (ValueVector v2) = do
                                             q' <- rownumM pos' [resCol, pos] Nothing $ rowrank resCol [(descr, Asc), (item, Asc)] v1
                                             d1 <- distinctM $ proj [(descr, descr), (pos, resCol)] q'
                                             p <- proj [(posold, pos), (posnew, pos')] q'
                                             v <- tagM "groupBy ValueVector" $ projM [(descr, descr), (pos, pos), (item, item)]
                                                    $ eqJoinM pos'' pos' (proj [(descr, resCol), (pos, pos'), (pos'', pos)] q')
                                                                         (proj [(pos', pos), (item, item)] v2)
                                             return $ TupleVector [DescrVector d1, ValueVector v, PropVector p]
groupByPF (ValueVector v1) (DescrVector v2) = do
                                             q' <- rownumM pos' [resCol, pos] Nothing $ rowrank resCol [(descr, Asc), (item, Asc)] v1
                                             d1 <- distinctM $ proj [(descr, descr), (pos, resCol)] q'
                                             p <- proj [(posold, pos), (posnew, pos')] q'
                                             v <- projM [(descr, descr), (pos, pos), (item, item)]
                                                    $ eqJoinM pos'' pos' (proj [(descr, resCol), (pos, pos'), (pos'', pos)] q')
                                                                         (proj [(pos', pos)] v2)
                                             return $ TupleVector [DescrVector d1, DescrVector v, PropVector p]
groupByPF _ _ = error "groupBy: Should not be possible"

notPrimPF :: Plan -> Graph PFAlgebra Plan
notPrimPF (PrimVal q) = PrimVal <$> (projM [(pos, pos), (descr, descr), (item, tmpCol)] $ notC tmpCol item q)
notPrimPF _ = error "notPrimPF: Should not be possible"

notVecPF :: Plan -> Graph PFAlgebra Plan
notVecPF (ValueVector d) = ValueVector <$> (projM [(pos, pos), (descr, descr), (item, tmpCol)] $ notC tmpCol item d)
notVecPF _ = error "notVecPF: Should not be possible"

lengthAPF :: Plan -> Graph PFAlgebra Plan
lengthAPF (DescrVector d) = PrimVal <$> (attachM descr natT (nat 1) $ attachM pos natT (nat 1) $ aggrM [(Max, item, Just item)] Nothing $ (litTable (int 0) item intT) `unionM` (aggrM [(Count, item, Nothing)] Nothing $ proj [(pos, pos)] d))
lengthAPF (ValueVector d) = PrimVal <$> (attachM descr natT (nat 1) $ attachM pos natT (nat 1) $ aggrM [(Max, item, Just item)] Nothing $ (litTable (int 0) item intT) `unionM` (aggrM [(Count, item, Nothing)] Nothing $ proj [(pos, pos)] d))
lengthAPF _ = error "lengthAPF: Should not be possible"

lengthSegPF :: Plan -> Plan -> Graph PFAlgebra Plan
lengthSegPF (DescrVector q1) (ValueVector d) = ValueVector <$> (rownumM pos [descr] Nothing $ aggrM [(Max, item, Just item)] (Just descr) $ (attachM item intT (int 0) $ proj [(descr, pos)] q1) `unionM` (aggrM [(Count, item, Nothing)] (Just descr) $ proj [(descr, descr)] d))
lengthSegPF (DescrVector q1) (DescrVector d) = ValueVector <$> (rownumM pos [descr] Nothing $ aggrM [(Max, item, Just item)] (Just descr) $ (attachM item intT (int 0) $ proj [(descr, pos)] q1) `unionM` (aggrM [(Count, item, Nothing)] (Just descr) $ proj [(descr, descr)] d))
lengthSegPF _ _ = error "lengthSegPF: Should not be possible"

descToPropPF :: Plan -> Graph PFAlgebra Plan
descToPropPF (DescrVector q1) = PropVector <$> proj [(posnew, descr), (posold, pos)] q1
descToPropPF _ = error "descToPropPF: Should not be possible"

notAPF :: Plan -> Graph PFAlgebra Plan
notAPF (PrimVal q1) = PrimVal <$> projM [(pos, pos), (descr, descr), (item, resCol)] (notC resCol item q1)
notAPF (ValueVector q1) = ValueVector <$> projM [(pos, pos), (descr, descr), (item, resCol)] (notC resCol item q1)
notAPF _ = error "notAPF: Should not be possible"

outerPF :: Plan -> Graph PFAlgebra Plan
outerPF (NestedVector p _) = return $ DescrVector p
outerPF (ValueVector p)    = DescrVector <$> (tagM "outerPF" $ proj [(pos, pos), (descr,descr)] p)
outerPF e                  = error $ "outerPF: Can't extract outerPF plan" ++ show e
                
distPrimPF :: Plan -> Plan -> Graph PFAlgebra Plan
distPrimPF (PrimVal q1) d = do
                 (DescrVector q2) <- toDescr d
                 ValueVector <$> crossM (proj [(item, item)] q1) (return q2)
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
                    qr2 <- PropVector <$> proj [(posold, pos'), (posnew, pos)] q
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
propagateInPF p e = error $ "propagateInPF: Should not be possible\n" ++ show p ++ "\n\n" ++ show e
                     
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
segmentPF e = 
    do
     (rf, q, pf) <- determineResultVector e
     rf <$> proj (pf [(descr, pos), (pos, pos)]) q

restrictVecPF :: Plan -> Plan -> Graph PFAlgebra Plan
restrictVecPF e1 (ValueVector qm) = do
                    (rf, q1, pf) <- determineResultVector e1
                    q <- rownumM pos'' [pos] Nothing $ selectM resCol $ eqJoinM pos pos' (return q1) $ proj [(pos', pos), (resCol, item)] qm
                    qr <- rf <$> proj (pf [(pos, pos''), (descr, descr)]) q
                    qp <- PropVector <$> proj [(posold, pos), (posnew, pos'')] q
                    return $ TupleVector [qr, qp]
restrictVecPF _ _ = error "restrictVecPF: Should not be possible"

combineVecPF :: Plan -> Plan -> Plan -> Graph PFAlgebra Plan
combineVecPF (ValueVector qb) e1 e2 = do
                        (rf, q1, q2, pf) <- determineResultVector' e1 e2
                        d1 <- projM [(pos', pos'), (pos, pos)] $ rownumM pos' [pos] Nothing $ select item qb
                        d2 <- projM [(pos', pos'), (pos, pos)] $ rownumM pos' [pos] Nothing $ selectM resCol $ notC resCol item qb
                        q <- eqJoinM pos' posold (return d1) (proj (pf [(posold, pos), (descr, descr)]) q1) `unionM` eqJoinM pos' posold (return d2) (proj (pf [(posold, pos), (descr, descr)]) q2)
                        qr <- rf <$> proj (pf [(descr, descr), (pos, pos)]) q
                        qp1 <- PropVector <$> proj [(posold, pos'), (posnew, pos)] d1
                        qp2 <- PropVector <$> proj [(posold, pos'), (posnew, pos)] d2
                        return $ TupleVector [qr, qp1, qp2]
combineVecPF _ _ _ = error "combineVecPF: Should not be possible"
                        
bPermuteVecPF :: Plan -> Plan -> Graph PFAlgebra Plan
bPermuteVecPF e1 (ValueVector q2) = do
                     (rf, q1, pf) <- determineResultVector e1
                     q <- eqJoinM pos pos' (return q1) $ proj [(pos', pos), (posnew, item)] q2
                     qr <- rf <$> proj (pf [(descr, descr), (pos, posnew)]) q
                     qp <- PropVector <$> proj [(posold, pos), (posnew, posnew)] q
                     return $ TupleVector [qr, qp]
bPermuteVecPF _ _ = error "bpermuteVecPF: Should not be possible"

-- constructLiteralPF :: VectorAlgebra a => Ty.Type -> Val -> Graph a Plan
constructLiteralPF :: Ty.Type -> Val -> Graph PFAlgebra Plan
constructLiteralPF t (List es) = listToPlan t (zip (repeat 1) es)
constructLiteralPF (Ty.Pair t1 t2) (Pair e1 e2) = TupleVector <$> sequence [constructLiteralPF t1 e1, constructLiteralPF t2 e2]
constructLiteralPF _t v = PrimVal <$> (tagM "constant" $ (attachM descr natT (nat 1) $ attachM pos natT (nat 1) $ constructLiteralPF' v))
 where
  constructLiteralPF' (Int i) = litTable (int $ fromIntegral i) item intT
  constructLiteralPF' (Bool b) = litTable (bool b) item boolT
  constructLiteralPF' Unit     = litTable (int (-1)) item intT  
  constructLiteralPF' (String s) = litTable (string s) item stringT
  constructLiteralPF' (Double d) = litTable (double d) item doubleT
  constructLiteralPF' (List _) = $impossible 
  constructLiteralPF' (Pair _ _) = $impossible

-- listToPlan :: VectorAlgebra a => Typ.Type -> [(Integer, Val)] -> Graph a Plan
listToPlan :: Ty.Type -> [(Integer, Val)] -> Graph PFAlgebra Plan
listToPlan (Ty.List t@(Ty.List _)) [] = do
                                               d <- emptyTable [(descr, natT), (pos, natT)]
                                               v <- listToPlan t []
                                               return $ NestedVector d v
listToPlan (Ty.List t@(Ty.List _)) vs = do
                                          let (vals, rec) = unzip [([nat i, nat p], zip (repeat p) es) | (p, (i, List es)) <- zip [1..] vs]
                                          d <- litTable' vals  [(descr, natT), (pos, natT)]
                                          v <- listToPlan t $ concat rec
                                          return $ NestedVector d v                                                    
listToPlan (Ty.List t) [] = ValueVector <$> emptyTable [(descr, natT), (pos, natT), (item, algTy t)]
listToPlan (Ty.List t) vs = ValueVector <$> litTable' [[nat i, nat p, toAlgVal v] | (p, (i, v)) <- zip [1..] vs] [(descr, natT), (pos, natT), (item, algTy t)]
listToPlan _ _ = $impossible "Not a list value or type"
       
algTy :: Ty.Type -> ATy
algTy (Ty.Int) = intT
algTy (Ty.Double) = doubleT
algTy (Ty.Bool) = boolT
algTy (Ty.String) = stringT
algTy (Ty.Unit) = intT
algTy (Ty.Nat) = natT
algTy (Ty.Var _) = $impossible
algTy (Ty.Fn _ _) = $impossible
algTy (Ty.Pair _ _) = $impossible
algTy (Ty.List _) = $impossible

toAlgVal :: Val -> AVal
toAlgVal (Int i) = int $ fromIntegral i
toAlgVal (Bool b) = bool b
toAlgVal Unit = int (-1)
toAlgVal (String s) = string s
toAlgVal (Double d) = double d
toAlgVal (List _) = $impossible "Not a primitive value"
toAlgVal (Pair _ _) = $impossible

-- | Construct a name that represents a lifted variable in the environment.                        
constrEnvName :: String -> Int -> String
constrEnvName x 0 = x
constrEnvName x i = x ++ "<%>" ++ show i

tableRefPF :: String -> [FKL.TypedColumn Ty.Type] -> [FKL.Key] -> Graph PFAlgebra Plan
tableRefPF n cs ks = do
                     table <- dbTable n (renameCols cs) ks
                     t' <- attachM descr natT (nat 1) $ rownum pos keyItems Nothing table
                     cs' <- mapM (\(_, i) -> ValueVector <$> proj [(descr, descr), (pos, pos), (item, item ++ show i)] t') numberedCols 
                     return $ foldl1 (\x y -> TupleVector [y,x]) $ reverse cs'
  where
    renameCols :: [FKL.TypedColumn Ty.Type] -> [Column]
    renameCols xs = [NCol cn [Col i $ algTy t] | ((cn, t), i) <- zip xs [1..]]
    numberedCols = zip cs [1 :: Integer .. ]
    numberedColNames = map (\(c, i) -> (fst c, i)) numberedCols
    keyItems = map (\c -> "item" ++ (show $ fromJust $ lookup c numberedColNames)) (head ks)

toDescr :: Plan -> Graph PFAlgebra Plan
toDescr v@(DescrVector _) = return v
toDescr (ValueVector n)   = DescrVector <$> tagM "toDescr" (proj [(descr, descr), (pos, pos)] n)
toDescr _ = error "toDescr: Should not be possible"

ifPrimListPF :: Plan -> Plan -> Plan -> Graph PFAlgebra Plan
ifPrimListPF qb (PrimVal q1) (PrimVal q2) = (\(ValueVector v) -> PrimVal v) <$> ifPrimListPF qb (ValueVector q1) (ValueVector q2)
ifPrimListPF (PrimVal qb) (ValueVector q1) (ValueVector q2) = ValueVector <$>
    do
     projM [(descr, descr), (pos, pos), (item, item)] $ 
        selectM tmpCol $ 
            unionM 
                (crossM (pure q1) (proj [(tmpCol, item)] qb))
                (crossM (pure q2) (projM [(tmpCol, item')] (notC item' item qb)))
ifPrimListPF _ _ _ = $impossible

-- FIXME abstract and move to VectorPrimitives
determineResultVector :: Plan -> Graph a (AlgNode -> Plan, AlgNode, ProjInf -> ProjInf)
determineResultVector e = do
                             let hasI = isValueVector e
                             let rf = if hasI then ValueVector else DescrVector
                             let pf = if hasI then \x -> (item, item):x else \x -> x
                             let q = if hasI
                                         then let (ValueVector q') = e in q'
                                         else let (DescrVector q') = e in q'
                             return (rf, q, pf)

determineResultVector' :: Plan -> Plan -> Graph a (AlgNode -> Plan, AlgNode, AlgNode, ProjInf -> ProjInf)
determineResultVector' e1 e2 = do
                                 let hasI = isValueVector e1
                                 let rf = if hasI then ValueVector else DescrVector
                                 let pf = if hasI then \x -> (item, item):x else \x -> x
                                 let (q1, q2) = if hasI
                                                 then let (ValueVector q1') = e1
                                                          (ValueVector q2') = e2 in (q1', q2')
                                                 else let (DescrVector q1') = e1 
                                                          (DescrVector q2') = e2 in (q1', q2')
                                 return (rf, q1, q2, pf)
