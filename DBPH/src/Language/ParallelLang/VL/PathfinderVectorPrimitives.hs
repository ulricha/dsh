{-# LANGUAGE TemplateHaskell #-}
module Language.ParallelLang.VL.PathfinderVectorPrimitives where

import Data.Maybe

import Control.Applicative hiding (Const)

import Language.ParallelLang.Common.Impossible
import Language.ParallelLang.Common.Data.Val
import Language.ParallelLang.Common.Data.Op
import qualified Language.ParallelLang.Common.Data.Type as Ty
import qualified Language.ParallelLang.FKL.Data.FKL as FKL
import Language.ParallelLang.VL.Data.Vector hiding (Pair)
import Language.ParallelLang.VL.Data.DBVector 
import qualified Language.ParallelLang.VL.Data.Vector as V
import Language.ParallelLang.VL.VectorPrimitives

import Database.Algebra.Pathfinder
import Database.Algebra.Dag.Common
import Database.Algebra.Dag.Builder

import System.IO.Unsafe

instance VectorAlgebra PFAlgebra where

  groupBy = groupByPF
  -- notA = notAPF
  notPrim = notPrimPF
  notVec = notVecPF
  lengthA = lengthAPF
  lengthSeg = lengthSegPF
  descToRename = descToRenamePF
  -- outer = outerPF
  distPrim = distPrimPF
  distDesc = distDescPF
  distLift = distLiftPF
  propRename = propRenamePF
  propFilter = propFilterPF
  propReorder = propReorderPF
  -- singletonVec = singletonVecPF
  singletonDescr = singletonDescrPF
  append = appendPF
  segment = segmentPF
  restrictVec = restrictVecPF
  combineVec = combineVecPF
  -- bPermuteVec = bPermuteVecPF
  constructLiteral = mkLiteral
  tableRef = tableRefPF
  binOp = binOpPF
  binOpL = binOpLPF
  -- emptyVector = emptyVectorPF
  -- ifPrimList = ifPrimListPF
  sortWith = sortWithPF
  vecSum = vecSumPF
  vecSumLift = vecSumLiftPF
  selectPos = selectPosPF
  selectPosLift = selectPosLiftPF
  -- empty = emptyPF
  -- emptyLift = emptyLiftPF
  projectA (DBP q _) pc = flip DBP [1..length pc] <$> (tagM "projectA" $ proj ([(descr, descr), (pos, pos)] ++ [(itemi n, itemi c) | (c, n) <- zip pc [1..] ]) q)
  projectL (DBV q _) pc = flip DBV [1..length pc] <$> (tagM "projectL" $ proj ([(descr, descr), (pos, pos)] ++ [(itemi n, itemi c) | (c, n) <- zip pc [1..] ]) q)
  toDescr = toDescrPF
  zipA (DBP q1 cols1) (DBP q2 cols2) = do
                                        (r, cols') <- doZip (q1, cols1) (q2, cols2)
                                        return $ DBP r cols'
  zipL (DBV q1 cols1) (DBV q2 cols2) = do
                                        (r, cols') <- doZip (q1, cols1) (q2, cols2)
                                        return $ DBV r cols'

doZip :: (AlgNode, [DBCol]) -> (AlgNode, [DBCol]) -> Graph PFAlgebra (AlgNode, [DBCol])
doZip (q1, cols1) (q2, cols2) = do
                               let offSet = length cols1
                               let cols' = cols1 ++ map (+offSet) cols2 
                               r <- projM ((descr, descr):(pos, pos):[ (itemi i, itemi i) | i <- cols']) $
                                 eqJoinM pos pos'
                                  (return q1)
                                  $ proj ((pos', pos):[ (itemi $ i + offSet, itemi i) | i <- cols2 ]) q2 
                               return (r, cols')

-- | Results are stored in column:
pos, item', item, descr, descr', descr'', pos', pos'', pos''', posold, posnew, ordCol, resCol, tmpCol, tmpCol' :: AttrName
pos       = "pos"
item      = "item1"
item'     = "item99999991"
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
{-
emptyVectorPF :: (Maybe Ty.Type) -> Graph PFAlgebra Plan
emptyVectorPF Nothing  = DescrVector <$> (emptyTable $ map (\(x,y) -> (algCol x, algTy y)) [(AuxCol Descr, Ty.Nat), (AuxCol Pos, Ty.Nat)])
emptyVectorPF (Just t) = case t of
                          (Ty.List (Ty.Pair t1 t2)) -> do
                                                       e1 <- emptyVectorPF (Just $ Ty.List t1)
                                                       e2 <- emptyVectorPF (Just $ Ty.List t2)
                                                       return $ PairVector e1 e2
                          (Ty.List t'@(Ty.List _)) -> do
                                                    (DescrVector dv) <- emptyVectorPF Nothing
                                                    nv <- emptyVectorPF (Just t')
                                                    return $ NestedVector dv nv
                          (Ty.List t')             -> let infos = [(AuxCol Descr, Ty.Nat), (AuxCol Pos, Ty.Nat), (AuxCol Item, t')] 
                                                       in ValueVector <$> (emptyTable $ map (\(x,y) -> (algCol x, algTy y)) infos)
                          _                        -> error $ "Can't generate an empty list for an expression of type: " ++ show t
-}   
                        
selectPosLiftPF :: DBV -> Oper -> DBV -> Graph PFAlgebra (DBV, RenameVector)
selectPosLiftPF (DBV qe cols) op (DBV qi _) =
    do
        let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols]
        qs <- rownumM posnew [descr, pos] Nothing
              $ selectM resCol
              $ operM (show op) resCol pos' item'
              $ eqJoinM descr pos''
              (rownum pos' [pos] (Just descr) qe)
              (proj [(pos'', pos), (item', item)] qi)
        q <- proj (pf [(descr, descr), (pos, posnew)]) qs
        qp <- proj [(posold, pos), (posnew, posnew)] qs
        return $ (DBV q cols, RenameVector qp)
selectPosLiftPF _ _ _ = $impossible

selectPosPF :: DBV -> Oper -> Plan -> Graph PFAlgebra (DBV, RenameVector)
selectPosPF (DBV qe cols) op (PrimVal _ qi) =
    do
        let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols]
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
        return $ (DBV q cols, RenameVector qp)
selectPosPF _ _ _ = $impossible
{-
emptyPF :: Plan -> Graph PFAlgebra Plan
emptyPF e =
    do
        (_, q, _) <- determineResultVector e
        qs <- operM "==" resCol item' tmpCol 
              $ attachM item' natT (nat 0)
              $ aggr [(Max, tmpCol, Nothing)] Nothing q
        qe <- projM [(descr, descr), (pos, pos), (item, item)]
              $ attachM item boolT (bool True) 
              $ select resCol qs
        qne <- projM [(descr, descr), (pos, pos), (item, item)]
              $ attachM item boolT (bool False) 
              $ select resCol qs
        qu <- attachM pos natT (nat 1)
              $ attachM descr natT (nat 1)
              $ union qe qne
        return $ ValueVector qu

emptyLiftPF :: Plan -> Plan -> Graph PFAlgebra Plan
emptyLiftPF (DescrVector qo) ei =
    do
        (_, qi, _) <- determineResultVector ei
        qd <- distinctM
              $ proj [(descr, descr)] qi
        qe <- attachM item boolT (bool True)
              $ attachM pos natT (nat 1)
              $ (differenceM
                 (proj [(descr, descr)] qo)
                 (return qd))
        qne <- attachM pos natT (nat 1)
               $ attach item boolT (bool False) qd
        qu <- union qe qne
        return $ ValueVector qu
emptyLiftPF _ _ = $impossible
-}
vecSumPF :: Ty.Type -> DBV -> Graph PFAlgebra DBP
vecSumPF t (DBV q _) =
    do
        q' <- attachM pos natT (nat 1) 
                $ attachM descr natT (nat 1) $
                 case t of
                    Ty.Int -> litTable (int 0) item intT
                    Ty.Nat -> litTable (nat 0) item natT
                    Ty.Double -> litTable (double 0) item doubleT
                    _   -> error "This type is not supported by the sum primitive (PF)"
        qs <- attachM descr natT (nat 1)
             $ attachM pos natT (nat 1)
             $ aggrM [(Sum, item, Just item)] Nothing
             $ union q' q
        return $ DBP qs [1]

vecSumLiftPF :: DescrVector -> DBV -> Graph PFAlgebra DBV
vecSumLiftPF (DescrVector qd) (DBV qv _) =
    do
        qe <- attachM item intT (int 0) -- TODO: In general you do not know that it should be an int, it might be double or nat...
              $ attachM pos natT (nat 1)
              $ differenceM
                (proj [(descr, pos)] qd)
                (proj [(descr, descr)] qv)
        qs <- rownumM pos [descr] Nothing
              $ aggr [(Sum, item, Just item)] (Just descr) qv
        qr <- union qe qs
        -- align the result vector with the original descriptor vector to get
        -- the proper descriptor values (sum removes one list type constructor)
        qa <- projM [(descr, descr'), (pos, pos), (item, item)]
              $ (eqJoinM pos' descr
                 (proj [(descr', descr), (pos', pos)] qd)
                 (return qr))
        return $ DBV qa [1]

applyBinOp :: Oper -> AlgNode -> AlgNode -> Graph PFAlgebra AlgNode
applyBinOp op q1 q2 =
  projM [(item, resCol), (descr, descr), (pos, pos)] 
    $ operM (show op) resCol item tmpCol 
    $ eqJoinM pos pos' (return q1) 
    $ proj [(tmpCol, item), (pos', pos)] q2

binOpLPF :: Oper -> DBV -> DBV -> Graph PFAlgebra DBV
binOpLPF op (DBV q1 _) (DBV q2 _) | op == GtE = do
                                             q1' <- applyBinOp Gt q1 q2
                                             q2' <- applyBinOp Eq q1 q2
                                             flip DBV [1] <$> applyBinOp Disj q1' q2'
                              | op == LtE = do
                                             q1' <- applyBinOp Lt q1 q2
                                             q2' <- applyBinOp Eq q1 q2
                                             flip DBV [1] <$> applyBinOp Disj q1' q2'
                              | otherwise = flip DBV [1] <$> applyBinOp op q1 q2

binOpPF :: Oper -> DBP -> DBP -> Graph PFAlgebra DBP
binOpPF op (DBP q1 _) (DBP q2 _) | op == GtE = do
                                            q1' <- applyBinOp Gt q1 q2
                                            q2' <- applyBinOp Eq q1 q2
                                            flip DBP [1] <$> applyBinOp Disj q1' q2'
                             | op == LtE = do
                                           q1' <- applyBinOp Lt q1 q2
                                           q2' <- applyBinOp Eq q1 q2
                                           flip DBP [1] <$> applyBinOp Disj q1' q2'
                             | otherwise = flip DBP [1] <$> applyBinOp op q1 q2
                                             
sortWithPF :: DBV -> DBV -> Graph PFAlgebra (DBV, PropVector)
sortWithPF (DBV qs colss) (DBV qe colse) = 
    do
        let pf = \x -> x ++ [(itemi i, itemi i) | i <- colse]
        q <- tagM "sortWith" 
             $ eqJoinM pos pos''
               (projM [(pos, pos), (pos', pos')]
                $ rownum pos' (descr : [itemi i | i <- colss] ++ [pos]) Nothing qs)
               (proj (pf [(descr, descr), (pos'', pos)]) qe)
        qv <- proj (pf [(descr, descr), (pos, pos')]) q
        qp <- proj [(posold, pos''), (posnew, pos')] q
        return $ (DBV qv colse, PropVector qp)

groupByPF :: DBV -> DBV -> Graph PFAlgebra (DescrVector, DBV, PropVector)
groupByPF (DBV v1 colsg) (DBV v2 colse) = do
                                             q' <- rownumM pos' [resCol, pos] Nothing $ rowrank resCol ((descr, Asc):[(itemi i, Asc) | i<- colsg]) v1
                                             d1 <- distinctM $ proj [(descr, descr), (pos, resCol)] q'
                                             p <- proj [(posold, pos), (posnew, pos')] q'
                                             v <- tagM "groupBy ValueVector" $ projM [(descr, descr), (pos, pos), (item, item)]
                                                    $ eqJoinM pos'' pos' (proj [(descr, resCol), (pos, pos'), (pos'', pos)] q')
                                                                         (proj ((pos', pos):[(itemi i, itemi i) | i <- colse]) v2)
                                             return $ (DescrVector d1, DBV v colse, PropVector p)

notPrimPF :: DBP -> Graph PFAlgebra DBP
notPrimPF (DBP q _) = flip DBP [1] <$> (projM [(pos, pos), (descr, descr), (item, tmpCol)] $ notC tmpCol item q)


notVecPF :: DBV -> Graph PFAlgebra DBV
notVecPF (DBV d _) = flip DBV [1] <$> (projM [(pos, pos), (descr, descr), (item, tmpCol)] $ notC tmpCol item d)

lengthAPF :: DescrVector -> Graph PFAlgebra DBP
lengthAPF (DescrVector d) = flip DBP [1] <$> (attachM descr natT (nat 1) $ attachM pos natT (nat 1) $ aggrM [(Max, item, Just item)] Nothing $ (litTable (int 0) item intT) `unionM` (aggrM [(Count, item, Nothing)] Nothing $ proj [(pos, pos)] d))

lengthSegPF :: DescrVector -> DescrVector -> Graph PFAlgebra DBV
lengthSegPF (DescrVector q1) (DescrVector d) = flip DBV [1] <$> (rownumM pos [descr] Nothing $ aggrM [(Max, item, Just item)] (Just descr) $ (attachM item intT (int 0) $ proj [(descr, pos)] q1) `unionM` (aggrM [(Count, item, Nothing)] (Just descr) $ proj [(descr, descr)] d))

descToRenamePF :: DescrVector -> Graph PFAlgebra RenameVector
descToRenamePF (DescrVector q1) = RenameVector <$> proj [(posnew, descr), (posold, pos)] q1

{-
notAPF :: Plan -> Graph PFAlgebra Plan
notAPF (PrimVal q1) = PrimVal <$> projM [(pos, pos), (descr, descr), (item, resCol)] (notC resCol item q1)
notAPF (ValueVector q1) = ValueVector <$> projM [(pos, pos), (descr, descr), (item, resCol)] (notC resCol item q1)
notAPF _ = error "notAPF: Should not be possible"

outerPF :: Plan -> Graph PFAlgebra Plan
outerPF (PairVector e1 _e2) = outerPF e1
outerPF (NestedVector p _) = return $ DescrVector p
outerPF (ValueVector p)    = DescrVector <$> (tagM "outerPF" $ proj [(pos, pos), (descr,descr)] p)
outerPF e                  = error $ "outerPF: Can't extract outerPF plan" ++ show e
-}      
distPrimPF :: DBP -> DescrVector -> Graph PFAlgebra (DBV, PropVector)
distPrimPF (DBP q1 cols) (DescrVector q2) = do
                 qr <- crossM (proj [(itemi i, itemi i) | i <- cols] q1) (return q2)
                 r <- proj [(posnew, pos), (posold, descr)] q2
                 return (DBV qr cols, PropVector r)
                  
distDescPF :: DBV -> DescrVector -> Graph PFAlgebra (DBV, PropVector)
distDescPF (DBV q1 cols) (DescrVector q2) = do
                   let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols ]
                   q <- projM (pf [(descr, pos), (pos, pos''), (posold, posold)]) $ rownumM pos'' [pos, pos'] Nothing $ crossM (proj [(pos, pos)] q2) (proj (pf [(pos', pos), (posold, pos)]) q1)
                   qr1 <- flip DBV cols <$> proj (pf [(descr, descr), (pos, pos)]) q
                   qr2 <- PropVector <$> proj [(posold, posold), (posnew, pos)] q
                   return $ (qr1, qr2)

distLiftPF :: DBV -> DescrVector -> Graph PFAlgebra (DBV, PropVector)
distLiftPF (DBV q1 cols) (DescrVector q2) = do
                    let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols]
                    q <- eqJoinM pos' descr (proj (pf [(pos', pos)]) q1) $ return q2
                    qr1 <- flip DBV cols <$> proj (pf [(descr, descr), (pos, pos)]) q
                    qr2 <- PropVector <$> proj [(posold, pos'), (posnew, pos)] q
                    return $ (qr1, qr2)                    

propRenamePF :: RenameVector -> DBV -> Graph PFAlgebra DBV
propRenamePF (RenameVector q1) (DBV q2 cols) = do
                let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols]
                q <- tagM "propRenamePF" $ projM (pf [(descr, posnew), (pos, pos)]) $ eqJoin posold descr q1 q2
                return $ DBV q cols
                
propFilterPF :: RenameVector -> DBV -> Graph PFAlgebra (DBV, RenameVector)
propFilterPF (RenameVector q1) (DBV q2 cols) = do
                     let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols]
                     q <- rownumM pos' [posnew, pos] Nothing $ eqJoin posold descr q1 q2
                     qr1 <- flip DBV cols <$> proj (pf [(descr, posnew), (pos, pos')]) q
                     qr2 <- RenameVector <$> proj [(posold, pos), (posnew, pos')] q
                     return $ (qr1, qr2)
                   
propReorderPF :: PropVector -> DBV -> Graph PFAlgebra (DBV, PropVector)
-- For Pathfinder algebra, the filter and reorder cases are the same, since numbering to generate positions
-- is done with a rownum and involves sorting.
propReorderPF (PropVector q1) e2 = do
                                 (p, (RenameVector r)) <- propFilterPF (RenameVector q1) e2
                                 return (p, PropVector r)
                     
singletonDescrPF :: Graph PFAlgebra DescrVector
singletonDescrPF = DescrVector <$> (tagM "singletonDescr" $ attachM pos natT (nat 1) $ litTable (nat 1) descr natT)
                   
appendPF :: DBV -> DBV -> Graph PFAlgebra (DBV, RenameVector, RenameVector)
appendPF (DBV q1 cols) (DBV q2 _) = do
                let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols]
                q <- rownumM pos' [descr, ordCol, pos] Nothing $ attach ordCol natT (nat 1) q1 `unionM` attach ordCol natT (nat 2) q2
                qv <- flip DBV cols <$> tagM "append r" (proj (pf [(pos, pos'), (descr, descr)]) q)
                qp1 <- RenameVector <$> (tagM "append r1" $ projM [(posold, pos), (posnew, pos')] $ selectM resCol $ operM "==" resCol ordCol tmpCol $ attach tmpCol natT (nat 1) q)
                qp2 <- RenameVector <$> (tagM "append r2" $ projM [(posold, pos), (posnew, pos')] $ selectM resCol $ operM "==" resCol ordCol tmpCol $ attach tmpCol natT (nat 2) q)
                return $ (qv, qp1, qp2)

segmentPF :: DBV -> Graph PFAlgebra DBV
segmentPF (DBV q cols) = 
    do
     let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols]
     flip DBV cols <$> proj (pf [(descr, pos), (pos, pos)]) q

restrictVecPF :: DBV -> DBV -> Graph PFAlgebra (DBV, RenameVector)
restrictVecPF (DBV q1 cols) (DBV qm _) = do
                    let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols]
                    q <- rownumM pos'' [pos] Nothing $ selectM resCol $ eqJoinM pos pos' (return q1) $ proj [(pos', pos), (resCol, item)] qm
                    qr <- flip DBV cols <$> proj (pf [(pos, pos''), (descr, descr)]) q
                    qp <- RenameVector <$> proj [(posold, pos), (posnew, pos'')] q
                    return $ (qr, qp)

combineVecPF :: DBV -> DBV -> DBV -> Graph PFAlgebra (DBV, RenameVector, RenameVector)
combineVecPF (DBV qb _) (DBV q1 cols) (DBV q2 _) = do
                        let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols]
                        d1 <- projM [(pos', pos'), (pos, pos)] $ rownumM pos' [pos] Nothing $ select item qb
                        d2 <- projM [(pos', pos'), (pos, pos)] $ rownumM pos' [pos] Nothing $ selectM resCol $ notC resCol item qb
                        q <- eqJoinM pos' posold (return d1) (proj (pf [(posold, pos), (descr, descr)]) q1) `unionM` eqJoinM pos' posold (return d2) (proj (pf [(posold, pos), (descr, descr)]) q2)
                        qr <- flip DBV cols <$> proj (pf [(descr, descr), (pos, pos)]) q
                        qp1 <- RenameVector <$> proj [(posnew, pos), (posold, pos')] d1
                        qp2 <- RenameVector <$> proj [(posnew, pos), (posold, pos')] d2
                        return $ (qr, qp1, qp2)
{-
bPermuteVecPF :: Plan -> Plan -> Graph PFAlgebra (Plan, PropVector)
bPermuteVecPF e1 (ValueVector q2) = do
                     (rf, q1, pf) <- determineResultVector e1
                     q <- eqJoinM pos pos' (return q1) $ proj [(pos', pos), (posnew, item)] q2
                     qr <- rf <$> proj (pf [(descr, descr), (pos, posnew)]) q
                     qp <- PropVector <$> proj [(posold, pos), (posnew, posnew)] q
                     return $ (qr, qp)
bPermuteVecPF _ _ = error "bpermuteVecPF: Should not be possible"
-}
{-
-- constructLiteralPF :: VectorAlgebra a => Ty.Type -> Val -> Graph a Plan
constructLiteralPF :: Ty.Type -> Val -> Graph PFAlgebra Plan
constructLiteralPF t (List es) = listToPlan t (zip (repeat 1) es)
constructLiteralPF (Ty.Pair t1 t2) (Pair e1 e2) = PairVector <$> constructLiteralPF t1 e1 <*> constructLiteralPF t2 e2
constructLiteralPF _t v = PrimVal <$> (tagM "constant" $ (attachM descr natT (nat 1) $ attachM pos natT (nat 1) $ constructLiteralPF' v))
 where
  constructLiteralPF' (Int i) = litTable (int $ fromIntegral i) item intT
  constructLiteralPF' (Bool b) = litTable (bool b) item boolT
  constructLiteralPF' Unit     = litTable (int (-1)) item intT  
  constructLiteralPF' (String s) = litTable (string s) item stringT
  constructLiteralPF' (Double d) = litTable (double d) item doubleT
  constructLiteralPF' (List _) = $impossible 
  constructLiteralPF' (Pair _ _) = $impossible
-}

algVal :: Val -> AVal
algVal (Int i) = int (fromIntegral i)
algVal (Bool t) = bool t
algVal Unit = int (-1)
algVal (String s) = string s
algVal (Double d) = double d

mkLiteral :: Ty.Type -> Val -> Graph PFAlgebra Plan
mkLiteral t@(Ty.List _) (List es) = do
                                          ((descHd, descV), layout, _) <- toPlan (mkDescriptor [length es]) t 1 es
                                          case descV of
                                            [] -> (ValueVector layout) <$> emptyTable (reverse descHd)
                                            _  -> (ValueVector layout) <$> (flip litTable' (reverse descHd) $ map reverse descV)
mkLiteral (Ty.Fn _ _) _ = error "Not supported"
mkLiteral t e           = do
                          ((descHd, descV), layout, _) <- toPlan (mkDescriptor [1]) (Ty.List t) 1 [e]
                          PrimVal layout <$> flip litTable' (reverse descHd) (map reverse descV)

toPlan :: Table -> Ty.Type -> Int -> [Val] -> Graph PFAlgebra (Table, Layout AlgNode, Int)
toPlan (descHd, descV) (Ty.List t) c es = case t of
                                           (Ty.Pair t1 t2) -> do 
                                                               let (e1s, e2s) = unzip $ map splitVal es
                                                               (desc', l1, c') <- toPlan (descHd, descV) (Ty.List t1) c e1s
                                                               (desc'', l2, c'') <- toPlan desc' (Ty.List t2) c' e2s
                                                               return (desc'', V.Pair l1 l2, c'')
                                           (Ty.List t') -> do
                                                            let vs = map fromListVal es
                                                            let d = mkDescriptor $ map length vs
                                                            ((hd, vs), l, _) <- toPlan d t 1 (concat vs)
                                                            n <- case vs of 
                                                                    [] -> emptyTable (reverse hd)
                                                                    _ -> flip litTable' (reverse hd) (map reverse vs)
                                                            return ((descHd, descV), Nest n l, c)

                                           (Ty.Fn _ _) -> error "Function are not db values"
                                           _ -> let (hd, vs) = mkColumn c t es
                                                 in return ((hd:descHd, zipWith (:) vs descV), (InColumn c), c + 1)
toPlan _ (Ty.Fn _ _) _ _ = undefined
toPlan (descHd, descV) t c v = let (hd, v') = mkColumn c t v
                            in return $ ((hd:descHd, zipWith (:) v' descV), (InColumn c), c + 1)

fromListVal :: Val -> [Val]
fromListVal (List es) = es
fromListVal _              = error "fromListVal: Not a list"

splitVal :: Val -> (Val, Val)
splitVal (Pair e1 e2) = (e1, e2)
splitVal _                 = error $ "splitVal: Not a tuple" 


itemi :: Int -> String
itemi i = "item" ++ show i

mkColumn :: Int -> Ty.Type -> [Val] -> ((String, ATy), [AVal])
mkColumn i t vs = ((itemi i, algTy t), [algVal v | v <- vs]) 

type Table = ([(String, ATy)], [[AVal]])

mkDescriptor :: [Int] -> Table
mkDescriptor lengths = let header = [(pos, algTy Ty.Nat),(descr, algTy Ty.Nat)]
                           body = map (\(d, p) -> [nat $ fromIntegral p, nat $ fromIntegral d]) $ zip (concat [ replicate l p | (p, l) <- zip [1..] lengths] ) [1..]
                        in (header, body)

{-
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
-}       
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
{-
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
-}
tableRefPF :: String -> [FKL.TypedColumn] -> [FKL.Key] -> Graph PFAlgebra Plan
tableRefPF n cs ks = do
                     table <- dbTable n (renameCols cs) keyItems
                     t' <- attachM descr natT (nat 1) $ rownum pos (head keyItems) Nothing table
                     cs' <- tagM "table" $ proj ((descr, descr):(pos, pos):[(itemi i, itemi i) | i <- [1..length cs]]) t' 
                     return $ ValueVector (foldr1 V.Pair [InColumn i | i <- [1..length cs]]) cs'
  where
    renameCols :: [FKL.TypedColumn] -> [Column]
    renameCols xs = [NCol cn [Col i $ algTy t] | ((cn, t), i) <- zip xs [1..]]
    numberedCols = zip cs [1 :: Integer .. ]
    numberedColNames = map (\(c, i) -> (fst c, i)) numberedCols
    keyItems = map (map (\c -> "item" ++ (show $ fromJust $ lookup c numberedColNames))) ks

toDescrPF :: DBV -> Graph PFAlgebra DescrVector
toDescrPF (DBV n _)   = DescrVector <$> tagM "toDescr" (proj [(descr, descr), (pos, pos)] n)

{-
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
-}