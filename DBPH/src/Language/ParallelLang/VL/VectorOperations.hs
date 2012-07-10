{-# LANGUAGE TemplateHaskell #-}
module Language.ParallelLang.VL.VectorOperations where

import Language.ParallelLang.Common.Impossible

import Database.Algebra.VL.Data (VL(), VLVal(..))

import Language.ParallelLang.VL.Data.GraphVector
import Language.ParallelLang.VL.Data.DBVector
import Language.ParallelLang.VL.VLPrimitives hiding (prop)
import Language.ParallelLang.VL.MetaPrimitives
import Language.ParallelLang.Common.Data.Op
import Language.ParallelLang.Common.Data.Type hiding (Pair)
import qualified Language.ParallelLang.Common.Data.Type as T
import qualified Language.ParallelLang.Common.Data.Val as V
import Language.ParallelLang.FKL.Data.FKL (TypedColumn, Key)

import Control.Applicative

takeWithS ::  Plan -> Plan -> Graph VL Plan
takeWithS (ValueVector qb (InColumn 1)) (ValueVector q lyt) = do
                                                               (qb', _, _) <- (qb `append`) =<< constructLiteralTable [boolT] [[VLNat 1, VLNat 1, VLBool False]] 
                                                               qfs <- falsePositions qb'
                                                               one <- constructLiteralValue [intT] [VLNat 1, VLNat 1, VLInt 1]
                                                               (p, _) <- selectPos qfs Eq one
                                                               (r, prop) <- selectPos q Lt =<< only p 
                                                               lyt' <- chainRenameFilter prop lyt
                                                               return $ ValueVector r lyt'
takeWithS _ _ = error "takeWithS: Should not be possible"

dropWithS ::  Plan -> Plan -> Graph VL Plan
dropWithS (ValueVector qb (InColumn 1)) (ValueVector q lyt) =
    do
        (qb', _, _) <- (qb `append`) =<< constructLiteralTable [boolT] [[VLNat 1, VLNat 1, VLBool False]]
        minF <- vecMin =<< falsePositions qb'
        (r, prop) <- selectPos q GtE minF
        lyt' <- chainRenameFilter prop lyt
        return $ ValueVector r lyt' 
dropWithS _ _ = error "dropWithS: Should not be possible"

takeWithL ::  Plan -> Plan -> Graph VL Plan
takeWithL (ValueVector _ (Nest qb (InColumn 1))) (ValueVector qd (Nest q lyt)) = 
            do
             f <- constructLiteralValue [boolT] [VLNat 1, VLNat 1, VLBool False]
             (fs, _) <- distPrim f =<< toDescr qd
             (qb', _, _) <- append qb =<< segment fs
             qfs <- falsePositions qb'
             one <- constructLiteralValue [intT] [VLNat 1, VLNat 1, VLInt 1]
             (ones, _) <- distPrim one =<< toDescr qd
             (p, _) <- selectPosLift qfs Eq ones
             (r, prop) <- selectPosLift q Lt p
             lyt' <- chainRenameFilter prop lyt
             return $ ValueVector qd (Nest r lyt')
takeWithL _ _ = error "takeWithL: Should not be possible"

dropWithL ::  Plan -> Plan -> Graph VL Plan
dropWithL (ValueVector _ (Nest qb (InColumn 1))) (ValueVector qd (Nest q lyt)) =
            do
             f <- constructLiteralValue [boolT] [VLNat 1, VLNat 1, VLBool False]
             (fs, _ ) <- distPrim f =<< toDescr qd
             (qb', _, _) <- append qb =<< segment fs
             minF <- vecMinLift =<< falsePositions qb'
             (r, prop) <- selectPosLift q GtE minF
             lyt' <- chainRenameFilter prop lyt
             return $ ValueVector qd (Nest r lyt')
dropWithL _ _ = error "dropWithL: Should not be possible"

zipPrim ::  Plan -> Plan -> Graph VL Plan
zipPrim (ValueVector q1 lyt1) (ValueVector q2 lyt2) = do
                                                       q' <- pairL q1 q2
                                                       return $ ValueVector q' $ zipLayout lyt1 lyt2
zipPrim _ _ = error "zipPrim: Should not be possible"

zipLift ::  Plan -> Plan -> Graph VL Plan
zipLift (ValueVector d1 (Nest q1 lyt1)) (ValueVector _ (Nest q2 lyt2)) = do
    (q', r1, r2) <- zipL q1 q2
    lyt1' <- chainRenameFilter r1 lyt1
    lyt2' <- chainRenameFilter r2 lyt2
    return $ ValueVector d1 (Nest q' $ zipLayout lyt1' lyt2')
zipLift _ _ = error "zipLift: Should not be possible"

takePrim ::  Plan -> Plan -> Graph VL Plan
takePrim (PrimVal i (InColumn 1)) (ValueVector q lyt) = do
                                                         (q', r) <- selectPos q LtE i
                                                         lyt' <- chainRenameFilter r lyt
                                                         return $ ValueVector q' lyt'
takePrim _ _ = error "takePrim: Should not be possible"

takeLift ::  Plan -> Plan -> Graph VL Plan
takeLift (ValueVector is (InColumn 1)) (ValueVector d (Nest q lyt)) = do
                                            (q', r) <- selectPosLift q LtE is
                                            lyt' <- chainRenameFilter r lyt
                                            return $ ValueVector d (Nest q' lyt')
takeLift _ _ = error "takeLift: Should not be possible"

dropPrim ::  Plan -> Plan -> Graph VL Plan
dropPrim (PrimVal i (InColumn 1)) (ValueVector q lyt) = do
                                                         (q', r) <- selectPos q Gt i
                                                         lyt' <- chainRenameFilter r lyt
                                                         return $ ValueVector q' lyt'
dropPrim _ _ = error "dropPrim: Should not be possible"

dropLift ::  Plan -> Plan -> Graph VL Plan
dropLift (ValueVector is (InColumn 1)) (ValueVector d (Nest q lyt)) = do
                                            (q', r) <- selectPosLift q Gt is
                                            lyt' <- chainRenameFilter r lyt
                                            return $ ValueVector d (Nest q' lyt')
dropLift _ _ = error "dropLift: Should not be possible"

nubPrim ::  Plan -> Graph VL Plan
nubPrim (ValueVector q lyt) = flip ValueVector lyt <$> unique q
nubPrim _ = error "nubPrim: Should not be possible" 

nubLift ::  Plan -> Graph VL Plan
nubLift (ValueVector d (Nest q lyt)) =  ValueVector d . flip Nest lyt <$> uniqueL q
nubLift _ = error "nubLift: Should not be possible"

initPrim ::  Plan -> Graph VL Plan
initPrim (ValueVector q lyt) = do
                                 i <- lengthA =<< toDescr q
                                 (q', r) <- selectPos q Lt i
                                 lyt' <- chainRenameFilter r lyt
                                 return $ ValueVector q' lyt'
initPrim _ = error "initPrim: Should not be possible"

initLift ::  Plan -> Graph VL Plan
initLift (ValueVector qs (Nest q lyt)) = do
                                          d <- toDescr qs
                                          is <- lengthSeg d =<< toDescr q
                                          (q', r) <- selectPosLift q Lt is
                                          lyt' <- chainRenameFilter r lyt
                                          return $ ValueVector qs (Nest q' lyt')
initLift _ = error "initLift: Should not be possible"

lastPrim ::  Plan -> Graph VL Plan
lastPrim (ValueVector qs lyt@(Nest _ _)) = do
                                               i <- lengthA =<< toDescr qs
                                               (q, r) <- selectPos qs Eq i
                                               (Nest qr lyt') <- chainRenameFilter r lyt
                                               re <- descToRename =<< toDescr q
                                               renameOuter re $ ValueVector qr lyt'
lastPrim (ValueVector qs lyt) = do
                                    i <- lengthA =<< toDescr qs
                                    (q, r) <- selectPos qs Eq i
                                    lyt' <- chainRenameFilter r lyt
                                    flip PrimVal lyt' <$> only q
lastPrim _ = error "lastPrim: Should not be possible"

lastLift ::  Plan -> Graph VL Plan
lastLift (ValueVector d (Nest qs lyt@(Nest _ _))) = do
                                                      ds <- toDescr d
                                                      is <- lengthSeg ds =<< toDescr qs
                                                      (qs', r) <- selectPosLift qs Eq is
                                                      lyt' <- chainRenameFilter r lyt
                                                      re <- descToRename =<< toDescr qs'
                                                      ValueVector d <$> renameOuter' re lyt'
lastLift (ValueVector d (Nest qs lyt)) = do
                                          ds <- toDescr d
                                          is <- lengthSeg ds =<< toDescr qs
                                          (qs', r) <- selectPosLift qs Eq is
                                          lyt' <- chainRenameFilter r lyt
                                          re <- descToRename =<< toDescr d
                                          renameOuter re (ValueVector qs' lyt')
lastLift _ = error "lastLift: Should not be possible"

indexPrim ::  Plan -> Plan -> Graph VL Plan
indexPrim (ValueVector qs lyt@(Nest _ _)) (PrimVal i _) = do
                                                           i' <-  binOp Add i =<< constructLiteralValue [intT] [VLNat 1, VLNat 1, VLInt 1]
                                                           (q, r) <- selectPos qs Eq i'
                                                           (Nest qr lyt') <- chainRenameFilter r lyt
                                                           re <- descToRename =<< toDescr q
                                                           renameOuter re $ ValueVector qr lyt'
indexPrim (ValueVector qs lyt) (PrimVal i _) = do
                                                i' <-  binOp Add i =<< constructLiteralValue [intT] [VLNat 1, VLNat 1, VLInt 1]
                                                (q, r) <- selectPos qs Eq i'
                                                lyt' <- chainRenameFilter r lyt
                                                flip PrimVal lyt' <$> only q
indexPrim _ _ = error "indexPrim: Should not be possible"

indexLift ::  Plan -> Plan -> Graph VL Plan
indexLift (ValueVector d (Nest qs lyt@(Nest _ _))) (ValueVector is (InColumn 1)) = do
                                                                         ds <- toDescr is
                                                                         (ones, _) <- (flip distPrim ds) =<< constructLiteralValue [intT] [VLNat 1, VLNat 1, VLInt 1]
                                                                         is' <- binOpL Add is ones
                                                                         (qs', r) <- selectPosLift qs Eq is'
                                                                         lyt' <- chainRenameFilter r lyt
                                                                         re <- descToRename =<< toDescr qs'
                                                                         ValueVector d <$> renameOuter' re lyt'
indexLift (ValueVector d (Nest qs lyt)) (ValueVector is (InColumn 1)) = do
                                                                         ds <- toDescr is
                                                                         (ones, _) <- (flip distPrim ds) =<< constructLiteralValue [intT] [VLNat 1, VLNat 1, VLInt 1]
                                                                         is' <- binOpL Add is ones
                                                                         (qs', r) <- selectPosLift qs Eq is'
                                                                         lyt' <- chainRenameFilter r lyt
                                                                         re <- descToRename =<< toDescr d
                                                                         renameOuter re (ValueVector qs' lyt')
indexLift _ _ = error "indexLift: Should not be possible"

appendPrim ::  Plan -> Plan -> Graph VL Plan
appendPrim = appendR 

appendLift ::  Plan -> Plan -> Graph VL Plan
appendLift (ValueVector d lyt1) (ValueVector _ lyt2) = ValueVector d <$> appendR' lyt1 lyt2
appendLift _ _ = error "appendLift: Should not be possible"
    
reversePrim ::  Plan -> Graph VL Plan
reversePrim (ValueVector d lyt) = do
                                (d', p) <- reverseA d
                                lyt' <- chainReorder p lyt
                                return (ValueVector d' lyt')
reversePrim _ = error "reversePrim: Should not be possible"

reverseLift ::  Plan -> Graph VL Plan
reverseLift (ValueVector d (Nest d1 lyt)) = do
                                        (d1', p) <- reverseL d1
                                        lyt' <- chainReorder p lyt
                                        return (ValueVector d (Nest d1' lyt'))
reverseLift _ = error "reverseLift: Should not be possible"

andPrim ::  Plan -> Graph VL Plan
andPrim (ValueVector d (InColumn 1)) = do
                                        p <- constructLiteralTable [boolT] [[VLNat 1, VLNat 1, VLBool True]]
                                        (r, _, _) <- append p d
                                        v <- vecMin r
                                        return $ PrimVal v (InColumn 1)
andPrim _ = error "andPrim: Should not be possible"

andLift ::  Plan -> Graph VL Plan
andLift (ValueVector d (Nest q (InColumn 1))) = do
                                                 d' <- toDescr d
                                                 t <- constructLiteralValue [boolT] [VLNat 1, VLNat 1, VLBool True]
                                                 (ts, _) <- distPrim t d'
                                                 ts' <- segment ts
                                                 (res, _, _) <- append ts' q
                                                 minLift (ValueVector d (Nest res (InColumn 1)))
andLift _ = error "andLift: Should not be possible"

orPrim ::  Plan -> Graph VL Plan
orPrim (ValueVector d (InColumn 1)) = do
                                        p <- constructLiteralTable [boolT] [[VLNat 1, VLNat 1, VLBool False]]
                                        (r, _, _) <- append p d
                                        v <- vecMax r
                                        return $ PrimVal v (InColumn 1)
orPrim _ = error "orPrim: Should not be possible"

orLift ::  Plan -> Graph VL Plan
orLift (ValueVector d (Nest q (InColumn 1))) = do
                                                 d' <- toDescr d
                                                 t <- constructLiteralValue [boolT] [VLNat 1, VLNat 1, VLBool False]
                                                 (ts, _) <- distPrim t d'
                                                 ts' <- segment ts
                                                 (res, _, _) <- append ts' q
                                                 maxLift (ValueVector d (Nest res (InColumn 1)))
orLift _ = error "orLift: Should not be possible"

                                        
the ::  Plan -> Graph VL Plan
the (ValueVector d lyt@(Nest _ _)) = do
                                     p <- constructLiteralValue [intT] [VLNat 1, VLNat 1, VLInt 1]
                                     (_, prop) <- selectPos d Eq p
                                     (Nest q' lyt') <- chainRenameFilter prop lyt
                                     return $ ValueVector q' lyt'
the (ValueVector d lyt) = do
                            p <- constructLiteralValue [intT] [VLNat 1, VLNat 1, VLInt 1]
                            (q', prop) <- selectPos d Eq p
                            lyt' <- chainRenameFilter prop lyt
                            flip PrimVal lyt' <$> only q'
the _ = error "the: Should not be possible"

tailS ::  Plan -> Graph VL Plan
tailS (ValueVector d lyt) = do
                             p <- constructLiteralValue [intT] [VLNat 1, VLNat 1, VLInt 1]
                             (q', prop) <- selectPos d Gt p
                             lyt' <- chainRenameFilter prop lyt
                             return $ ValueVector q' lyt'
tailS _ = error "tailS: Should not be possible"

theL ::  Plan -> Graph VL Plan
theL (ValueVector d (Nest q lyt)) = do
                                      one <- constructLiteralValue [intT] [VLNat 1, VLNat 1, VLInt 1]
                                      (p, _) <- distPrim one =<< toDescr d
                                      (v, p2) <- selectPosLift q Eq p 
                                      prop <- descToRename =<< toDescr d
                                      lyt' <- chainRenameFilter p2 lyt
                                      (v', _) <- propFilter prop v
                                      return $ ValueVector v' lyt'
theL _ = error "theL: Should not be possible" 

tailL ::  Plan -> Graph VL Plan
tailL (ValueVector d (Nest q lyt)) = do
                                      one <- constructLiteralValue [intT] [VLNat 1, VLNat 1, VLInt 1]
                                      (p, _) <- distPrim one =<< toDescr d
                                      (v, p2) <- selectPosLift q Gt p
                                      lyt' <- chainRenameFilter p2 lyt
                                      return $ ValueVector d (Nest v lyt')
tailL _ = error "tailL: Should not be possible"

sortWithS ::  Plan -> Plan -> Graph VL Plan
sortWithS (ValueVector q1 _) (ValueVector q2 lyt2) = do
                                   (v, p) <- sortWith q1 q2
                                   lyt2' <- chainReorder p lyt2
                                   return $ ValueVector v lyt2'
sortWithS _e1 _e2 = error "sortWithS: Should not be possible" 

sortWithL ::  Plan -> Plan -> Graph VL Plan
sortWithL (ValueVector _ (Nest v1 _)) (ValueVector d2 (Nest v2 lyt2)) = do
                                  (v, p) <- sortWith v1 v2
                                  lyt2' <- chainReorder p lyt2
                                  return $ ValueVector d2 (Nest v lyt2')
sortWithL _ _ = error "sortWithL: Should not be possible"

-- move a descriptor from e1 to e2
unconcatV ::  Plan -> Plan -> Graph VL Plan
unconcatV (ValueVector d1 _) (ValueVector d2 lyt2) = do
                                                         (DescrVector d') <- toDescr d1
                                                         return $ ValueVector (DBV d' []) (Nest d2 lyt2)
unconcatV _ _ = $impossible

groupByS ::  Plan -> Plan -> Graph VL Plan
groupByS (ValueVector q1 _) (ValueVector q2 lyt2) = do
                                            (DescrVector d, v, p) <- groupBy q1 q2
                                            lyt2' <- chainReorder p lyt2
                                            return $ ValueVector (DBV d []) (Nest v lyt2')
groupByS _e1 _e2 = error $ "groupByS: Should not be possible "

groupByL ::  Plan -> Plan -> Graph VL Plan
groupByL (ValueVector _ (Nest v1 _)) (ValueVector d2 (Nest v2 lyt2)) = do
                                        (DescrVector d, v, p) <- groupBy v1 v2
                                        lyt2' <- chainReorder p lyt2
                                        return $ ValueVector d2 (Nest (DBV d []) (Nest v lyt2'))
groupByL _ _ = error "groupByL: Should not be possible"

concatLift ::  Plan -> Graph VL Plan
concatLift (ValueVector d (Nest d' vs)) = do
                                                    p <- descToRename =<< (toDescr d')
                                                    vs' <- renameOuter' p vs
                                                    return $ ValueVector d vs'
concatLift _ = error "concatLift: Should not be possible"

lengthLift ::  Plan -> Graph VL Plan
lengthLift (ValueVector q (Nest qi _)) = do
                                            d <- toDescr q
                                            di <- toDescr qi
                                            ls <- lengthSeg d di
                                            p <- descToRename d
                                            r <- propRename p ls
                                            return $ ValueVector r (InColumn 1)
lengthLift _ = $impossible

lengthV ::  Plan -> Graph VL Plan
lengthV q = do
             v' <- outer q
             v <- lengthA v'
             return $ PrimVal v (InColumn 1)

cons ::  Plan -> Plan -> Graph VL Plan
cons q1@(PrimVal _ _) q2@(ValueVector _ _) = do
                                             n <- singletonPrim q1
                                             appendR n q2
cons q1 q2 = do
                n <- singletonVec q1
                appendR n q2

consLift ::  Plan -> Plan -> Graph VL Plan
consLift (ValueVector q1 lyt1) (ValueVector q2 (Nest qi lyt2)) = do
                        s <- segment q1
                        (v, p1, p2) <- append s qi
                        lyt1' <- renameOuter' p1 lyt1
                        lyt2' <- renameOuter' p2 lyt2
                        lyt' <- appendR' lyt1' lyt2'
                        return $ ValueVector q2 (Nest v lyt')
consLift _ _ = $impossible
                        

restrict ::  Plan -> Plan -> Graph VL Plan
restrict(ValueVector q1 lyt) (ValueVector q2 (InColumn 1))
                  = do
                      (v, p) <- restrictVec q1 q2
                      lyt' <- chainRenameFilter p lyt
                      return $ ValueVector v lyt'
restrict (AClosure n l i env arg e1 e2) bs = do
                                            l' <- restrict l bs
                                            env' <- mapEnv (flip restrict bs) env
                                            return $ AClosure n l' i env' arg e1 e2 
restrict e1 e2 = error $ "restrict: Can't construct restrict node " ++ show e1 ++ " " ++ show e2

combine ::  Plan -> Plan -> Plan -> Graph VL Plan
combine (ValueVector qb (InColumn 1)) (ValueVector q1 lyt1) (ValueVector q2 lyt2) =
                      do
                        (v, p1, p2) <- combineVec qb q1 q2
                        lyt1' <- renameOuter' p1 lyt1
                        lyt2' <- renameOuter' p2 lyt2
                        lyt' <- appendR' lyt1' lyt2'
                        return $ ValueVector v lyt'
combine _ _ _ = $impossible


outer ::  Plan -> Graph VL DescrVector
outer (PrimVal _ _) = $impossible
outer (ValueVector q _) = toDescr q
outer (Closure _ _ _ _ _) = $impossible
outer (AClosure _ v _ _ _ _ _) = outer v

dist ::  Plan -> Plan -> Graph VL Plan
dist (PrimVal q lyt) q2 = do
                           o <- outer q2
                           (v, p) <- distPrim q o
                           lyt' <- chainReorder p lyt
                           return $ ValueVector v lyt'
dist (ValueVector q lyt) q2 = do
                               o@(DescrVector qo) <- outer q2
                               (d, p) <- distDesc q o
                               lyt' <- chainReorder p lyt
                               return $ ValueVector (DBV qo []) (Nest d lyt')
dist (Closure n env x f fl) q2 = (\env' -> AClosure n q2 1 env' x f fl) <$> mapEnv (flip dist q2) env
dist _ _ = $impossible

mapEnv ::  (Plan -> Graph VL Plan) -> [(String, Plan)] -> Graph VL [(String, Plan)]
mapEnv f  ((x, p):xs) = (\p' xs' -> (x, p'):xs') <$> f p <*> mapEnv f xs
mapEnv _f []          = return []

minPrim ::  Plan -> Graph VL Plan
minPrim (ValueVector q (InColumn 1)) = flip PrimVal (InColumn 1) <$> vecMin q
minPrim _ = $impossible

minLift ::  Plan -> Graph VL Plan
minLift (ValueVector d (Nest q (InColumn 1))) = do
                                                 r <- descToRename =<< toDescr d
                                                 flip ValueVector (InColumn 1) <$> (propRename r =<< vecMinLift q)
minLift _ = $impossible

maxPrim ::  Plan -> Graph VL Plan
maxPrim (ValueVector q (InColumn 1)) = flip PrimVal (InColumn 1) <$> vecMax q
maxPrim _ = $impossible

maxLift ::  Plan -> Graph VL Plan
maxLift (ValueVector d (Nest q (InColumn 1))) = do
                                                    r <- descToRename =<< toDescr d
                                                    flip ValueVector (InColumn 1) <$> (propRename r =<< vecMaxLift q)
maxLift _ = $impossible

sumPrim ::  Type -> Plan -> Graph VL Plan
sumPrim t (ValueVector q (InColumn 1)) = flip PrimVal (InColumn 1) <$> vecSum t q
sumPrim _ _ = $impossible

sumLift ::   Plan -> Graph VL Plan
sumLift (ValueVector d1 (Nest q (InColumn 1))) = do
                                                  d <- toDescr d1
                                                  flip ValueVector (InColumn 1) <$> vecSumLift d q
sumLift _ = $impossible


distL ::  Plan -> Plan -> Graph VL Plan
distL (ValueVector q1 lyt1) (ValueVector d (Nest o _)) = do
                                                          (v, p) <- distLift q1 =<< toDescr o
                                                          lyt1' <- chainReorder p lyt1
                                                          return $ ValueVector d (Nest v lyt1')
distL (AClosure n v i xs x f fl) q2 = do
                                        v' <- distL v q2
                                        xs' <- mapEnv (\y -> distL y v') xs
                                        return $ AClosure n v' (i + 1) xs' x f fl
distL _e1 _e2 = error $ "distL: Should not be possible" ++ show _e1 ++ "\n" ++ show _e2


ifList ::  Plan -> Plan -> Plan -> Graph VL Plan
ifList (PrimVal qb _) (ValueVector q1 lyt1) (ValueVector q2 lyt2) =
    do
     (d1', _) <- distPrim qb =<< toDescr q1
     (d1, p1) <- restrictVec q1 d1'
     qb' <- notPrim qb
     (d2', _) <- distPrim qb' =<< toDescr q2
     (d2, p2) <- restrictVec q2 d2'
     r1 <- renameOuter' p1 lyt1
     r2 <- renameOuter' p2 lyt2
     lyt' <- appendR' r1 r2
     (d, _, _) <- append d1 d2
     return $ ValueVector d lyt'
ifList qb (PrimVal q1 lyt1) (PrimVal q2 lyt2) = do
                                                   q1' <- singleton q1
                                                   q2' <- singleton q2
                                                   (ValueVector q lyt) <- ifList qb (ValueVector q1' lyt1) (ValueVector q2' lyt2)
                                                   flip PrimVal lyt <$> only q
ifList _ _ _ = $impossible

pairOpL ::  Plan -> Plan -> Graph VL Plan
pairOpL (ValueVector q1 lyt1) (ValueVector q2 lyt2) = do
                                                     q <- pairL q1 q2
                                                     let lyt = zipLayout lyt1 lyt2
                                                     return $ ValueVector q lyt
pairOpL _ _ = $impossible

pairOp ::  Plan -> Plan -> Graph VL Plan
pairOp (PrimVal q1 lyt1) (PrimVal q2 lyt2) = do
                                             q <- pairA q1 q2
                                             let lyt = zipLayout lyt1 lyt2
                                             return $ PrimVal q lyt
pairOp (ValueVector q1 lyt1) (ValueVector q2 lyt2) = do
                                                    d <- constructLiteralValue [] [VLNat 1, VLNat 1]
                                                    let lyt = zipLayout (Nest q1 lyt1) (Nest q2 lyt2)
                                                    return $ PrimVal d lyt
pairOp (ValueVector q1 lyt1) (PrimVal q2 lyt2) = do
                                                 let lyt = zipLayout (Nest q1 lyt1) lyt2
                                                 return $ PrimVal q2 lyt
pairOp (PrimVal q1 lyt1) (ValueVector q2 lyt2) = do
                                                 let lyt = zipLayout lyt1 (Nest q2 lyt2)
                                                 return $ PrimVal q1 lyt
pairOp _ _ = $impossible

fstA ::  Plan -> Graph VL Plan   
fstA (PrimVal _q (Pair (Nest q lyt) _p2)) = return $ ValueVector q lyt
fstA (PrimVal q (Pair p1 _p2)) = do
                                     let (p1', cols) = projectFromPos p1
                                     proj <- projectA q cols
                                     return $ PrimVal proj p1'
fstA e1 = error $ "fstA: " ++ show e1                                                     

fstL ::  Plan -> Graph VL Plan   
fstL (ValueVector q (Pair p1 _p2)) = do
                                        let(p1', cols) = projectFromPos p1
                                        proj <- projectL q cols
                                        return $ ValueVector proj p1'
fstL _ = $impossible

sndA ::  Plan -> Graph VL Plan   
sndA (PrimVal _q (Pair _p1 (Nest q lyt))) = return $ ValueVector q lyt
sndA (PrimVal q (Pair _p1 p2)) = do
                                    let (p2', cols) = projectFromPos p2
                                    proj <- projectA q cols
                                    return $ PrimVal proj p2'
sndA _ = $impossible
    
sndL ::  Plan -> Graph VL Plan   
sndL (ValueVector q (Pair _p1 p2)) = do
                                        let (p2', cols) = projectFromPos p2
                                        proj <- projectL q cols
                                        return $ ValueVector proj p2'
sndL _ = $impossible

projectFromPos :: Layout -> (Layout, [DBCol])
projectFromPos = (\(x,y,_) -> (x,y)) . (projectFromPosWork 1)
    where
      projectFromPosWork :: Int -> Layout -> (Layout, [DBCol], Int)
      projectFromPosWork c (InColumn i)   = (InColumn c, [i], c + 1)
      projectFromPosWork c (Nest q l)       = (Nest q l, [], c)
      projectFromPosWork c (Pair p1 p2)   = let (p1', cols1, c') = projectFromPosWork c p1
                                                (p2', cols2, c'') = projectFromPosWork c' p2
                                             in (Pair p1' p2', cols1 ++ cols2, c'')
                                             
concatV :: Plan -> Graph VL Plan
concatV (ValueVector _ (Nest q lyt)) = return $ ValueVector q lyt
concatV (AClosure n v l fvs x f1 f2) | l > 1 = AClosure n <$> (concatV v) 
                                                          <*> pure (l - 1) 
                                                          <*> (mapM (\(y, val) -> do
                                                                                     val' <- concatV val
                                                                                     return (y, val')) fvs)
                                                          <*> pure x <*> pure f1 <*> pure f2
concatV e                  = error $ "Not supported by concatV: " ++ show e


singletonVec ::  Plan -> Graph VL Plan
singletonVec (ValueVector q lyt) = do
                                 (DescrVector d) <- singletonDescr
                                 return $ ValueVector (DBV d []) (Nest q lyt)
singletonVec _ = error "singletonVec: Should not be possible"

singletonPrim ::  Plan -> Graph VL Plan
singletonPrim (PrimVal q1 lyt) = flip ValueVector lyt <$> singleton q1
singletonPrim _ = error "singletonPrim: Should not be possible"

dbTable ::  String -> [TypedColumn] -> [Key] -> Graph VL Plan
dbTable n cs ks = do
                    t <- tableRef n (map (mapSnd typeToVLType) cs) ks
                    return $ ValueVector t (foldr1 Pair [InColumn i | i <- [1..length cs]])

mkLiteral ::  Type -> V.Val -> Graph VL Plan                    
mkLiteral t@(List _) (V.List es) = do
                                            ((descHd, descV), layout, _) <- toPlan (mkDescriptor [length es]) t 1 es
                                            (flip ValueVector layout) <$> (constructLiteralTable (reverse descHd) $ map reverse descV) 
mkLiteral (Fn _ _) _ = error "Not supported"
mkLiteral t e           = do
                            ((descHd, [descV]), layout, _) <- toPlan (mkDescriptor [1]) (List t) 1 [e]
                            flip PrimVal layout <$> constructLiteralValue (reverse descHd) (reverse descV)
                            
type Table = ([Type], [[VLVal]])

toPlan ::  Table -> Type -> Int -> [V.Val] -> Graph VL (Table, Layout, Int)
toPlan (descHd, descV) (List t) c es = case t of
                                             (T.Pair t1 t2) -> do 
                                                                 let (e1s, e2s) = unzip $ map splitVal es
                                                                 (desc', l1, c') <- toPlan (descHd, descV) (List t1) c e1s
                                                                 (desc'', l2, c'') <- toPlan desc' (List t2) c' e2s
                                                                 return (desc'', Pair l1 l2, c'')
                                             (List _) -> do
                                                              let vs = map fromListVal es
                                                              let d = mkDescriptor $ map length vs
                                                              ((hd, vs'), l, _) <- toPlan d t 1 (concat vs)
                                                              n <- constructLiteralTable (reverse hd) (map reverse vs')
                                                              return ((descHd, descV), Nest n l, c)
                                                                 
                                             (Fn _ _) -> error "Function are not db values"
                                             _ -> let (hd, vs) = mkColumn t es
                                                   in return ((hd:descHd, zipWith (:) vs descV), (InColumn c), c + 1)
toPlan _ (Fn _ _) _ _ = $impossible
toPlan (descHd, descV) t c v = let (hd, v') = mkColumn t v
                              in return $ ((hd:descHd, zipWith (:) v' descV), (InColumn c), c + 1)

fromListVal :: V.Val -> [V.Val]
fromListVal (V.List es) = es
fromListVal _              = error "fromListVal: Not a list"

splitVal :: V.Val -> (V.Val, V.Val)
splitVal (V.Pair e1 e2) = (e1, e2)
splitVal _                 = error $ "splitVal: Not a tuple" 


pVal :: V.Val -> VLVal
pVal (V.Int i) = VLInt i
pVal (V.Bool b) = VLBool b
pVal (V.String s) = VLString s
pVal (V.Double d) = VLDouble d
pVal V.Unit = VLUnit
pVal _ = error "pVal: Not a supported value"

mkColumn :: Type -> [V.Val] -> (Type, [VLVal])
mkColumn t vs = (t, [pVal v | v <- vs]) 
                                            
mkDescriptor :: [Int] -> Table
mkDescriptor lengths = let header = []
                           body = map (\(d, p) -> [VLNat $ fromIntegral p, VLNat $ fromIntegral d]) $ zip (concat [ replicate l p | (p, l) <- zip [1..] lengths] ) [1..]
                        in (header, body)