{-# LANGUAGE TemplateHaskell #-}
module Language.ParallelLang.VL.PathfinderVectorPrimitives() where

import Data.Maybe

import Control.Applicative hiding (Const)

import Language.ParallelLang.Common.Impossible
import qualified Language.ParallelLang.FKL.Data.FKL as FKL
import Language.ParallelLang.VL.Data.DBVector 
import Language.ParallelLang.VL.VectorPrimitives
import qualified Database.Algebra.VL.Data as VL

import Database.Algebra.Pathfinder
import Database.Algebra.Dag.Builder

instance VectorAlgebra PFAlgebra where
  groupBy = groupByPF
  notPrim = notPrimPF
  notVec = notVecPF
  lengthA = lengthAPF
  lengthSeg = lengthSegPF
  descToRename = descToRenamePF
  distPrim = distPrimPF
  distDesc = distDescPF
  distLift = distLiftPF
  propRename = propRenamePF
  propFilter = propFilterPF
  propReorder = propReorderPF
  singletonDescr = singletonDescrPF
  append = appendPF
  segment = segmentPF
  restrictVec = restrictVecPF
  combineVec = combineVecPF
  constructLiteralTable tys [] = flip DBV [1..length tys] <$> emptyTable ((descr, natT):(pos, natT):[(itemi i, algTy t) | (i, t) <- zip [1..] tys])
  constructLiteralTable tys vs = flip DBV [1..length tys] <$> (flip litTable' ((descr, natT):(pos, natT):[(itemi i, algTy t) | (i, t) <- zip [1..] tys]) $ map (map algVal) vs)       
  constructLiteralValue t v = (\(DBV v' cols) -> DBP v' cols) <$> constructLiteralTable t [v]
  
  tableRef = tableRefPF
  sortWith = sortWithPF
  vecMin = vecMinPF
  vecMinLift = vecMinLiftPF
  vecMax = vecMaxPF
  vecMaxLift = vecMaxLiftPF
  vecSum = vecSumPF
  vecSumLift = vecSumLiftPF
  selectPos = selectPosPF
  selectPos1 = undefined
  selectPosLift = selectPosLiftPF
  selectPos1Lift = undefined
  integerToDoubleA (DBP q _) = flip DBP [1] <$> (projM [(descr, descr), (pos, pos), (item, resCol)] $ cast item resCol doubleT q)
  integerToDoubleL (DBV q _) = flip DBV [1] <$> (projM [(descr, descr), (pos, pos), (item, resCol)] $ cast item resCol doubleT q)
  projectA (DBP q _) pc = flip DBP [1..length pc] <$> (tagM "projectA" $ proj ([(descr, descr), (pos, pos)] ++ [(itemi n, itemi c) | (c, n) <- zip pc [1..] ]) q)
  projectL (DBV q _) pc = flip DBV [1..length pc] <$> (tagM "projectL" $ proj ([(descr, descr), (pos, pos)] ++ [(itemi n, itemi c) | (c, n) <- zip pc [1..] ]) q)
  toDescr = toDescrPF
  zipL = undefined
  pairA (DBP q1 cols1) (DBP q2 cols2) = do
                                        (r, cols') <- doZip (q1, cols1) (q2, cols2)
                                        return $ DBP r cols'
  pairL (DBV q1 cols1) (DBV q2 cols2) = do
                                        (r, cols') <- doZip (q1, cols1) (q2, cols2)
                                        return $ DBV r cols'
  reverseA (DBV q cols) = do
                            let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols]
                            q' <- rownum' pos' [(pos, Desc)] Nothing q
                            r <- flip DBV cols <$> proj (pf [(descr, descr), (pos, pos')]) q'
                            p <- PropVector <$> proj [(posold, pos), (posnew, pos')] q'
                            return (r, p)
  reverseL (DBV q cols) = do
                            let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols]
                            q' <- rownum' pos' [(descr, Asc), (pos, Desc)] Nothing q
                            r <- flip DBV cols <$> proj (pf [(descr, descr), (pos, pos')]) q'
                            p <- PropVector <$> proj [(posold, pos), (posnew, pos')] q'
                            return (r, p)
  unique (DBV q cols) = do
                         let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols]
                         f <- rownumM posnew [posold] Nothing $ aggrM [(Min, posold, Just pos)] (Just resCol) $ rank resCol [(itemi i, Asc) | i <- cols] q
                         flip DBV cols <$> (projM (pf [(descr, descr), (pos, posnew)]) $ eqJoin pos posold q f)
  uniqueL (DBV q cols) = do
                          let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols]
                          f <- rownumM posnew [posold] Nothing $ aggrM [(Min, posold, Just pos)] (Just resCol) $ rank resCol ((descr, Asc):[(itemi i, Asc) | i <- cols]) q
                          flip DBV cols <$> (projM (pf [(descr, descr), (pos, posnew)]) $ eqJoin pos posold q f)
  falsePositions = undefined
  
  cartProductFlat = undefined
  
  thetaJoinFlat = undefined
  
  selectItem = undefined
  
  projectRename = undefined
                  
  projectValue = undefined
  
  compExpr1 = undefined
  compExpr2 = undefined
  compExpr2L = undefined

doZip :: (AlgNode, [DBCol]) -> (AlgNode, [DBCol]) -> GraphM r PFAlgebra (AlgNode, [DBCol])
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

selectPosLiftPF :: DBV -> VL.VecCompOp -> DBV -> GraphM r PFAlgebra (DBV, RenameVector)
selectPosLiftPF (DBV qe cols) op (DBV qi _) =
    do
        let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols]
        qx <- castM pos' pos''' intT 
                $ eqJoinM descr pos''
                    (rownum pos' [pos] (Just descr) qe)
                    (proj [(pos'', pos), (item', item)] qi)
        qs <- case op of
            VL.LtE -> rownumM posnew [descr, pos] Nothing
                  $ selectM resCol
                  $ unionM
                    (oper (show VL.Eq) resCol pos''' item' qx)
                    (oper (show VL.Lt) resCol pos''' item' qx)
            _ -> rownumM posnew [descr, pos] Nothing
                  $ selectM resCol
                  $ oper (show op) resCol pos''' item' qx
        q <- proj (pf [(descr, descr), (pos, posnew)]) qs
        qp <- proj [(posold, pos), (posnew, posnew)] qs
        return $ (DBV q cols, RenameVector qp)

selectPosPF :: DBV -> VL.VecCompOp -> DBP -> GraphM r PFAlgebra (DBV, RenameVector)
selectPosPF (DBV qe cols) op (DBP qi _) =
    do
        let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols]
        qx <- crossM
                (projM (pf [(descr,descr), (pos', pos')]) (cast pos pos' intT qe))
                -- (proj (pf [(descr, descr), (pos', pos)]) qe)
                (proj [(item', item)] qi)
        qn <- case op of
                VL.Lt ->
                    projM (pf [(descr, descr), (pos, pos'), (pos', pos')]) 
                     $ selectM resCol
                           $ oper (show op) resCol pos' item' qx
                VL.LtE ->
                    projM (pf [(descr, descr), (pos, pos'), (pos', pos')])
                     $ selectM resCol
                        $ unionM
                            (oper (show VL.Lt) resCol pos' item' qx)
                            (oper (show VL.Eq) resCol pos' item' qx)
                _ ->
                    projM (pf [(descr, descr), (pos, pos), (pos', pos')])
                     $ rownumM pos [descr, pos'] Nothing 
                        $ selectM resCol
                            $ oper (show op) resCol pos' item' qx
        q <- proj (pf [(descr, descr), (pos, pos)]) qn
        qp <- proj [(posnew, pos), (posold, pos')] qn
        return $ (DBV q cols, RenameVector qp)

vecMinPF :: DBV -> GraphM r PFAlgebra DBP
vecMinPF (DBV q _) = flip DBP [1] <$> (attachM descr natT (nat 1) $ attachM pos natT (nat 1) $ aggr [(Min, item, Just item)] Nothing q)

vecMaxPF :: DBV -> GraphM r PFAlgebra DBP
vecMaxPF (DBV q _) = flip DBP [1] <$> (attachM descr natT (nat 1) $ attachM pos natT (nat 1) $ aggr [(Max, item, Just item)] Nothing q)

vecSumPF :: VL.VLType -> DBV -> GraphM r PFAlgebra DBP
vecSumPF t (DBV q _) =
    do
        q' <- attachM pos natT (nat 1) 
                $ attachM descr natT (nat 1) $
                 case t of
                    VL.Int -> litTable (int 0) item intT
                    VL.Nat -> litTable (nat 0) item natT
                    VL.Double -> litTable (double 0) item doubleT
                    _   -> error "This type is not supported by the sum primitive (PF)"
        qs <- attachM descr natT (nat 1)
             $ attachM pos natT (nat 1)
             $ aggrM [(Sum, item, Just item)] Nothing
             $ union q' q
        return $ DBP qs [1]

vecMinLiftPF :: DBV -> GraphM r PFAlgebra DBV
vecMinLiftPF (DBV qv _) = flip DBV [1] <$> (projM [(descr,descr),(pos,pos),(item,item)] $ rownumM pos [descr] Nothing $ aggr [(Min, item, Just item)] (Just descr) qv)

vecMaxLiftPF :: DBV -> GraphM r PFAlgebra DBV
vecMaxLiftPF (DBV qv _) = flip DBV [1] <$> (projM [(descr,descr),(pos,pos),(item,item)] $ rownumM pos [descr] Nothing $ aggr [(Max, item, Just item)] (Just descr) qv)


vecSumLiftPF :: DescrVector -> DBV -> GraphM r PFAlgebra DBV
vecSumLiftPF (DescrVector qd) (DBV qv _) =
    do
        qe <- attachM item intT (int 0) -- TODO: In general you do not know that it should be an int, it might be double or nat...
              $ differenceM
                (proj [(descr, pos)] qd)
                (proj [(descr, descr)] qv)
        qs <- aggr [(Sum, item, Just item)] (Just descr) qv
        qr <- rownumM pos [descr] Nothing
              $ union qe qs
        -- align the result vector with the original descriptor vector to get
        -- the proper descriptor values (sum removes one list type constructor)
        qa <- projM [(descr, descr'), (pos, pos), (item, item)]
              $ (eqJoinM pos' descr
                 (proj [(descr', descr), (pos', pos)] qd)
                 (return qr))
        return $ DBV qa [1]

applyBinOp :: VL.VecOp -> AlgNode -> AlgNode -> GraphM r PFAlgebra AlgNode
applyBinOp op q1 q2 =
  projM [(item, resCol), (descr, descr), (pos, pos)] 
    $ operM (show op) resCol item tmpCol 
    $ eqJoinM pos pos' (return q1) 
    $ proj [(tmpCol, item), (pos', pos)] q2

binOpLPF :: VL.VecOp -> DBV -> DBV -> GraphM r PFAlgebra DBV
binOpLPF op (DBV q1 _) (DBV q2 _) | op == (VL.COp VL.GtE) = do
                                             q1' <- applyBinOp (VL.COp VL.Gt) q1 q2
                                             q2' <- applyBinOp (VL.COp VL.Eq) q1 q2
                                             flip DBV [1] <$> applyBinOp (VL.BOp VL.Disj) q1' q2'
                              | op == (VL.COp VL.LtE) = do
                                             q1' <- applyBinOp (VL.COp VL.Lt) q1 q2
                                             q2' <- applyBinOp (VL.COp VL.Eq) q1 q2
                                             flip DBV [1] <$> applyBinOp (VL.BOp VL.Disj) q1' q2'
                              | otherwise = flip DBV [1] <$> applyBinOp op q1 q2

binOpPF :: VL.VecOp -> DBP -> DBP -> GraphM r PFAlgebra DBP
binOpPF op (DBP q1 _) (DBP q2 _) | op == (VL.COp VL.GtE) = do
                                            q1' <- applyBinOp (VL.COp VL.Gt) q1 q2
                                            q2' <- applyBinOp (VL.COp VL.Eq) q1 q2
                                            flip DBP [1] <$> applyBinOp (VL.BOp VL.Disj) q1' q2'
                             | op == (VL.COp VL.LtE) = do
                                           q1' <- applyBinOp (VL.COp VL.Lt) q1 q2
                                           q2' <- applyBinOp (VL.COp VL.Eq) q1 q2
                                           flip DBP [1] <$> applyBinOp (VL.BOp VL.Disj) q1' q2'
                             | otherwise = flip DBP [1] <$> applyBinOp op q1 q2
                                             
sortWithPF :: DBV -> DBV -> GraphM r PFAlgebra (DBV, PropVector)
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

groupByPF :: DBV -> DBV -> GraphM r PFAlgebra (DescrVector, DBV, PropVector)
groupByPF (DBV v1 colsg) (DBV v2 colse) = do
                                             q' <- rownumM pos' [resCol, pos] Nothing $ rowrank resCol ((descr, Asc):[(itemi i, Asc) | i<- colsg]) v1
                                             d1 <- distinctM $ proj [(descr, descr), (pos, resCol)] q'
                                             p <- proj [(posold, pos), (posnew, pos')] q'
                                             v <- tagM "groupBy ValueVector" $ projM [(descr, descr), (pos, pos), (item, item)]
                                                    $ eqJoinM pos'' pos' (proj [(descr, resCol), (pos, pos'), (pos'', pos)] q')
                                                                         (proj ((pos', pos):[(itemi i, itemi i) | i <- colse]) v2)
                                             return $ (DescrVector d1, DBV v colse, PropVector p)

notPrimPF :: DBP -> GraphM r PFAlgebra DBP
notPrimPF (DBP q _) = flip DBP [1] <$> (projM [(pos, pos), (descr, descr), (item, tmpCol)] $ notC tmpCol item q)


notVecPF :: DBV -> GraphM r PFAlgebra DBV
notVecPF (DBV d _) = flip DBV [1] <$> (projM [(pos, pos), (descr, descr), (item, tmpCol)] $ notC tmpCol item d)

lengthAPF :: DescrVector -> GraphM r PFAlgebra DBP
lengthAPF (DescrVector d) = flip DBP [1] <$> (attachM descr natT (nat 1) $ attachM pos natT (nat 1) $ aggrM [(Max, item, Just item)] Nothing $ (litTable (int 0) item intT) `unionM` (aggrM [(Count, item, Nothing)] Nothing $ proj [(pos, pos)] d))

lengthSegPF :: DescrVector -> DescrVector -> GraphM r PFAlgebra DBV
lengthSegPF (DescrVector q1) (DescrVector d) = flip DBV [1] <$> (rownumM pos [descr] Nothing $ aggrM [(Max, item, Just item)] (Just descr) $ (attachM item intT (int 0) $ proj [(descr, pos)] q1) `unionM` (aggrM [(Count, item, Nothing)] (Just descr) $ proj [(descr, descr)] d))

descToRenamePF :: DescrVector -> GraphM r PFAlgebra RenameVector
descToRenamePF (DescrVector q1) = RenameVector <$> proj [(posnew, descr), (posold, pos)] q1

distPrimPF :: DBP -> DescrVector -> GraphM r PFAlgebra (DBV, PropVector)
distPrimPF (DBP q1 cols) (DescrVector q2) = do
                 qr <- crossM (proj [(itemi i, itemi i) | i <- cols] q1) (return q2)
                 r <- proj [(posnew, pos), (posold, descr)] q2
                 return (DBV qr cols, PropVector r)
                  
distDescPF :: DBV -> DescrVector -> GraphM r PFAlgebra (DBV, PropVector)
distDescPF (DBV q1 cols) (DescrVector q2) = do
                   let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols ]
                   q <- projM (pf [(descr, pos), (pos, pos''), (posold, posold)]) $ rownumM pos'' [pos, pos'] Nothing $ crossM (proj [(pos, pos)] q2) (proj (pf [(pos', pos), (posold, pos)]) q1)
                   qr1 <- flip DBV cols <$> proj (pf [(descr, descr), (pos, pos)]) q
                   qr2 <- PropVector <$> proj [(posold, posold), (posnew, pos)] q
                   return $ (qr1, qr2)

distLiftPF :: DBV -> DescrVector -> GraphM r PFAlgebra (DBV, PropVector)
distLiftPF (DBV q1 cols) (DescrVector q2) = do
                    let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols]
                    q <- eqJoinM pos' descr (proj (pf [(pos', pos)]) q1) $ return q2
                    qr1 <- flip DBV cols <$> proj (pf [(descr, descr), (pos, pos)]) q
                    qr2 <- PropVector <$> proj [(posold, pos'), (posnew, pos)] q
                    return $ (qr1, qr2)                    

propRenamePF :: RenameVector -> DBV -> GraphM r PFAlgebra DBV
propRenamePF (RenameVector q1) (DBV q2 cols) = do
                let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols]
                q <- tagM "propRenamePF" $ projM (pf [(descr, posnew), (pos, pos)]) $ eqJoin posold descr q1 q2
                return $ DBV q cols
                
propFilterPF :: RenameVector -> DBV -> GraphM r PFAlgebra (DBV, RenameVector)
propFilterPF (RenameVector q1) (DBV q2 cols) = do
                     let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols]
                     q <- rownumM pos' [posnew, pos] Nothing $ eqJoin posold descr q1 q2
                     qr1 <- flip DBV cols <$> proj (pf [(descr, posnew), (pos, pos')]) q
                     qr2 <- RenameVector <$> proj [(posold, pos), (posnew, pos')] q
                     return $ (qr1, qr2)
                   
propReorderPF :: PropVector -> DBV -> GraphM r PFAlgebra (DBV, PropVector)
-- For Pathfinder algebra, the filter and reorder cases are the same, since numbering to generate positions
-- is done with a rownum and involves sorting.
propReorderPF (PropVector q1) e2 = do
                                 (p, (RenameVector r)) <- propFilterPF (RenameVector q1) e2
                                 return (p, PropVector r)
                     
singletonDescrPF :: GraphM r PFAlgebra DescrVector
singletonDescrPF = DescrVector <$> (tagM "singletonDescr" $ attachM pos natT (nat 1) $ litTable (nat 1) descr natT)
                   
appendPF :: DBV -> DBV -> GraphM r PFAlgebra (DBV, RenameVector, RenameVector)
appendPF (DBV q1 cols) (DBV q2 _) = do
                let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols]
                q <- rownumM pos' [descr, ordCol, pos] Nothing $ attach ordCol natT (nat 1) q1 `unionM` attach ordCol natT (nat 2) q2
                qv <- flip DBV cols <$> tagM "append r" (proj (pf [(pos, pos'), (descr, descr)]) q)
                qp1 <- RenameVector <$> (tagM "append r1" $ projM [(posold, pos), (posnew, pos')] $ selectM resCol $ operM "==" resCol ordCol tmpCol $ attach tmpCol natT (nat 1) q)
                qp2 <- RenameVector <$> (tagM "append r2" $ projM [(posold, pos), (posnew, pos')] $ selectM resCol $ operM "==" resCol ordCol tmpCol $ attach tmpCol natT (nat 2) q)
                return $ (qv, qp1, qp2)

segmentPF :: DBV -> GraphM r PFAlgebra DBV
segmentPF (DBV q cols) = 
    do
     let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols]
     flip DBV cols <$> proj (pf [(descr, pos), (pos, pos)]) q

restrictVecPF :: DBV -> DBV -> GraphM r PFAlgebra (DBV, RenameVector)
restrictVecPF (DBV q1 cols) (DBV qm _) = do
                    let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols]
                    q <- rownumM pos'' [pos] Nothing $ selectM resCol $ eqJoinM pos pos' (return q1) $ proj [(pos', pos), (resCol, item)] qm
                    qr <- flip DBV cols <$> proj (pf [(pos, pos''), (descr, descr)]) q
                    qp <- RenameVector <$> proj [(posold, pos), (posnew, pos'')] q
                    return $ (qr, qp)

combineVecPF :: DBV -> DBV -> DBV -> GraphM r PFAlgebra (DBV, RenameVector, RenameVector)
combineVecPF (DBV qb _) (DBV q1 cols) (DBV q2 _) = do
                        let pf = \x -> x ++ [(itemi i, itemi i) | i <- cols]
                        d1 <- projM [(pos', pos'), (pos, pos)] $ rownumM pos' [pos] Nothing $ select item qb
                        d2 <- projM [(pos', pos'), (pos, pos)] $ rownumM pos' [pos] Nothing $ selectM resCol $ notC resCol item qb
                        q <- eqJoinM pos' posold (return d1) (proj (pf [(posold, pos), (descr, descr)]) q1) `unionM` eqJoinM pos' posold (return d2) (proj (pf [(posold, pos), (descr, descr)]) q2)
                        qr <- flip DBV cols <$> proj (pf [(descr, descr), (pos, pos)]) q
                        qp1 <- RenameVector <$> proj [(posnew, pos), (posold, pos')] d1
                        qp2 <- RenameVector <$> proj [(posnew, pos), (posold, pos')] d2
                        return $ (qr, qp1, qp2)

itemi :: Int -> String
itemi i = "item" ++ show i

algVal :: VL.VLVal -> AVal
algVal (VL.VLInt i) = int (fromIntegral i)
algVal (VL.VLBool t) = bool t  
algVal VL.VLUnit = int (-1)
algVal (VL.VLString s) = string s
algVal (VL.VLDouble d) = double d
algVal (VL.VLNat n) = nat $ fromIntegral n

algTy :: VL.VLType -> ATy
algTy (VL.Int) = intT
algTy (VL.Double) = doubleT
algTy (VL.Bool) = boolT
algTy (VL.String) = stringT
algTy (VL.Unit) = intT
algTy (VL.Nat) = natT
algTy (VL.Pair _ _) = $impossible
algTy (VL.VLList _) = $impossible

tableRefPF :: String -> [VL.TypedColumn] -> [FKL.Key] -> GraphM r PFAlgebra DBV
tableRefPF n cs ks = do
                     table <- dbTable n (renameCols cs) keyItems
                     t' <- attachM descr natT (nat 1) $ rownum pos (head keyItems) Nothing table
                     cs' <- tagM "table" $ proj ((descr, descr):(pos, pos):[(itemi i, itemi i) | i <- [1..length cs]]) t' 
                     return $ DBV cs' [1..length cs]
  where
    renameCols :: [VL.TypedColumn] -> [Column]
    renameCols xs = [NCol cn [Col i $ algTy t] | ((cn, t), i) <- zip xs [1..]]
    numberedCols = zip cs [1 :: Integer .. ]
    numberedColNames = map (\(c, i) -> (fst c, i)) numberedCols
    keyItems = map (map (\c -> "item" ++ (show $ fromJust $ lookup c numberedColNames))) ks

toDescrPF :: DBV -> GraphM r PFAlgebra DescrVector
toDescrPF (DBV n _)   = DescrVector <$> tagM "toDescr" (proj [(descr, descr), (pos, pos)] n)