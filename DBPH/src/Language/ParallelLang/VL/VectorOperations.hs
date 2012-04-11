{-# LANGUAGE TemplateHaskell #-}
module Language.ParallelLang.VL.VectorOperations where

import Language.ParallelLang.Common.Impossible

import Language.ParallelLang.VL.Data.Vector
import Language.ParallelLang.VL.Data.DBVector
import Language.ParallelLang.VL.VectorPrimitives
import Language.ParallelLang.VL.MetaPrimitives
import Language.ParallelLang.Common.Data.Op
-- import Language.ParallelLang.Common.Data.Type
import qualified Language.ParallelLang.Common.Data.Val as V

import Control.Applicative

{-
the :: VectorAlgebra a => Plan -> Graph a Plan
the e@(ValueVector _) = do
                         p <- constructLiteral intT (V.Int 1)
                         (ValueVector q, _) <- selectPos e Eq p
                         return $ PrimVal q
the (NestedVector d vs) = do
                            p <- constructLiteral intT (V.Int 1)
                            (_, prop) <- selectPos (DescrVector d) Eq p
                            chainRenameFilter prop vs
the (PairVector e1 e2) = PairVector <$> the e1 <*> the e2
the _ = error "the: Should not be possible"

theL :: VectorAlgebra a => Plan -> Graph a Plan
theL (NestedVector d e@(ValueVector _)) = do
                                            one <- constructLiteral intT (V.Int 1)
                                            p <- distPrim one (DescrVector d)
                                            (v, _) <- selectPosLift e Eq p
                                            prop <- descToRename (DescrVector d)
                                            (v', _) <- propFilter prop v
                                            return v' 
theL (NestedVector d (NestedVector d2 vs)) = do
                                            one <- constructLiteral intT (V.Int 1)
                                            p <- distPrim one (DescrVector d)
                                            (v, p2) <- selectPosLift (DescrVector d2) Eq p
                                            prop <- descToRename (DescrVector d)
                                            vs' <- chainRenameFilter p2 vs
                                            (v', _) <- propFilter prop v
                                            return $ attachV v' vs'
theL (PairVector e1 e2) = PairVector <$> theL e1 <*> theL e2
theL _ = error "theL: Should not be possible" 

sortWithS :: VectorAlgebra a => Plan -> Plan -> Graph a Plan
sortWithS e1 e2@(ValueVector _) = do
                                   (v, _) <- sortWith e1 e2
                                   return v
sortWithS e1 (NestedVector d2 vs2) = do
                                        (v, p) <- sortWith e1 (DescrVector d2)
                                        vs' <- chainReorder p vs2
                                        return $ attachV v vs'
sortWithS e1 (PairVector e1' e2') = PairVector <$> sortWithS e1 e1' <*> sortWithS e1 e2'
sortWithS _e1 _e2 = error "sortWithS: Should not be possible" 

sortWithL :: VectorAlgebra a => Plan -> Plan -> Graph a Plan
sortWithL (NestedVector _d1 v1@(ValueVector _)) (NestedVector d2 v2@(ValueVector _)) = do
                                  (v, _) <- sortWith v1 v2
                                  return $ attachV (DescrVector d2) v
sortWithL (NestedVector _d1 v1@(ValueVector _)) (NestedVector d2 (NestedVector d' vs2)) = do
                                     (v, p) <- sortWith v1 (DescrVector d')
                                     vs' <- chainReorder p vs2
                                     return $ attachV (DescrVector d2) $ attachV v vs'
sortWithL e1 (PairVector e1' e2') = PairVector <$> sortWithL e1 e1' <*> sortWithL e1 e2'
sortWithL _ _ = error "sortWithL: Should not be possible"

groupByS :: VectorAlgebra a => Plan -> Plan -> Graph a Plan
groupByS e1 e2@(ValueVector _) = do
                                  (d, v, _) <- groupBy e1 e2
                                  return $ attachV d v
groupByS e1 (NestedVector d2 vs2) = do
                                     (d, v, p) <- groupBy e1 (DescrVector d2)
                                     vs' <- chainReorder p vs2
                                     return $ attachV d $ attachV v vs'
groupByS e1 (PairVector e1' e2') = PairVector <$>  groupByS e1 e1' <*> groupByS e1 e2'
groupByS _e1 _e2 = error $ "groupByS: Should not be possible "

groupByL :: VectorAlgebra a => Plan -> Plan -> Graph a Plan
groupByL (NestedVector _d1 v1@(ValueVector _)) (NestedVector d2 v2@(ValueVector _)) = do
                                  (d, v, _) <- groupBy v1 v2
                                  return $ attachV (DescrVector d2) $ attachV d v
groupByL (NestedVector _d1 v1@(ValueVector _)) (NestedVector d2 (NestedVector d' vs2)) = do
                                     (d, v, p) <- groupBy v1 (DescrVector d')
                                     vs' <- chainReorder p vs2
                                     return $ attachV (DescrVector d2) $ attachV d $ attachV v vs'
groupByL e1 (PairVector e1' e2') = PairVector <$> groupByL e1 e1' <*> groupByL e1 e2'
groupByL _ _ = error "groupByL: Should not be possible"
-}                    
concatLift :: VectorAlgebra a => Plan -> Graph a Plan
concatLift (ValueVector (Nest d' vs) d) = do
                                                    p <- descToRename =<< (toDescr $ DBV d' $ snd $ projectFromPos vs)
                                                    vs' <- renameOuter' p vs
                                                    return $ ValueVector vs' d
concatLift _ = error "concatLift: Should not be possible"

lengthLift :: VectorAlgebra a => Plan -> Graph a Plan
lengthLift (ValueVector (Nest qi lyt) q) = do
                                            d <- toDescr (DBV q [])
                                            di <- toDescr (DBV qi $ snd $ projectFromPos lyt)
                                            ls <- lengthSeg d di
                                            p <- descToRename d
                                            (DBV r _) <- propRename p ls
                                            return $ ValueVector (InColumn 1) r

lengthV :: VectorAlgebra a => Plan -> Graph a Plan
lengthV v = do
             v' <- outer v
             (DBP v _) <- lengthA v'
             return $ PrimVal (InColumn 1) v

{-
consEmpty :: VectorAlgebra a => Plan -> Graph a Plan
consEmpty q@(PrimVal _) = singletonPrim q -- Corresponds to rule [cons-empty-1]
consEmpty q | nestingDepth q > 0 = singletonVec q
            | otherwise = error "consEmpty: Can't construct consEmpty node"
-}

cons :: VectorAlgebra a => Plan -> Plan -> Graph a Plan
cons q1@(PrimVal _ _) q2@(ValueVector _ _) = do
                                             n <- singletonPrim q1
                                             appendR n q2
cons q1 q2 = do
                n <- singletonVec q1
                appendR n q2
cons q1 q2 = error $ "cons: Should not be possible" ++ show q1 ++ "*******" ++ show q2


consLift :: VectorAlgebra a => Plan -> Plan -> Graph a Plan
consLift (ValueVector lyt1 q1) (ValueVector (Nest qi lyt2) q2) = do
                        s <- segment (DBV q1 $ snd $ projectFromPos lyt1)
                        (DBV v _, p1, p2) <- append s (DBV qi $ snd $ projectFromPos lyt2)
                        lyt1' <- renameOuter' p1 lyt1
                        lyt2' <- renameOuter' p2 lyt2
                        lyt' <- appendR' lyt1' lyt2'
                        return $ ValueVector (Nest v lyt') q2
                        
{-
restrict :: VectorAlgebra a => Plan -> Plan -> Graph a Plan
restrict (PairVector e1 e2) bs = do
                                        e1' <- restrict e1 bs
                                        e2' <- restrict e2 bs
                                        return $ PairVector e1' e2'
restrict e1@(ValueVector _) e2@(ValueVector _) 
                     -- Corresponds to compilation rule [restrict-1]
                   = do
                        (v, _) <- restrictVec e1 e2
                        return v

restrict (NestedVector d1 vs1) e2@(ValueVector _)
                     -- Corresponds to compilation rule [restrict-2]
                   = do
                       (v, p) <- restrictVec (DescrVector d1) e2
                       e3 <- chainRenameFilter p vs1
                       return $ attachV v e3
restrict (AClosure n l i env arg e1 e2) bs = do
                                            l' <- restrict l bs
                                            env' <- mapEnv (flip restrict bs) env
                                            return $ AClosure n l' i env' arg e1 e2 
restrict e1 e2 = error $ "restrict: Can't construct restrict node " ++ show e1 ++ " " ++ show e2

combine :: VectorAlgebra a => Plan -> Plan -> Plan -> Graph a Plan
combine eb (PairVector e11 e12) (PairVector e21 e22) = 
                     do
                         e1 <- combine eb e11 e21
                         e2 <- combine eb e12 e22
                         return $ PairVector e1 e2
combine eb e1 e2 | nestingDepth eb == 1 && nestingDepth e1 == 1 && nestingDepth e2 == 1
                      -- Corresponds to compilation rule [combine-1]
                    = do
                        (v, _, _) <- combineVec eb e1 e2
                        return v
                 | nestingDepth eb == 1 && nestingDepth e1 > 1 && nestingDepth e1 == nestingDepth e2
                      -- Corresponds to compilation rule [combine-2]
                    = do
                        let (NestedVector d1 vs1) = e1
                        let (NestedVector d2 vs2) = e2
                        (v, p1, p2) <- combineVec eb (DescrVector d1) (DescrVector d2)
                        r1 <- renameOuter p1 vs1
                        r2 <- renameOuter p2 vs2
                        e3 <- appendR r1 r2
                        return $ attachV v e3
                 | otherwise = error "combine: Can't construct combine node"

bPermute :: VectorAlgebra a => Plan -> Plan -> Graph a Plan
bPermute e1 e2 | nestingDepth e1 == 1 && nestingDepth e2 == 1
                    = do
                        (v, _) <- bPermuteVec e1 e2
                        return v
               | otherwise = error "bPermute: Can't construct bPermute node"
-}

outer :: VectorAlgebra a => Plan -> Graph a DescrVector
outer (PrimVal _ _) = $impossible
outer (ValueVector _ q) = toDescr (DBV q [])
outer (Closure _ _ _ _ _) = $impossible
outer (AClosure _ v _ _ _ _ _) = outer v

dist :: VectorAlgebra a => Plan -> Plan -> Graph a Plan
dist (PrimVal lyt q) q2 = do
                           o <- outer q2
                           (DBV v _, p) <- distPrim (DBP q $ snd $ projectFromPos lyt) o
                           lyt' <- chainRenameFilter p lyt
                           return $ ValueVector lyt' v
dist (ValueVector lyt q) q2 = do
                               o@(DescrVector qo) <- outer q2
                               (DBV d _, p) <- distDesc (DBV q $ snd $ projectFromPos lyt) o
                               lyt' <- chainRenameFilter p lyt
                               return $ ValueVector (Nest d lyt') qo
dist (Closure n env x f fl) q2 = (\env' -> AClosure n q2 1 env' x f fl) <$> mapEnv (flip dist q2) env

mapEnv :: VectorAlgebra a => (Plan -> Graph a Plan) -> [(String, Plan)] -> Graph a [(String, Plan)]
mapEnv f  ((x, p):xs) = (\p' xs' -> (x, p'):xs') <$> f p <*> mapEnv f xs
mapEnv _f []          = return []

{-

sumPrim :: VectorAlgebra a => Type -> Plan -> Graph a Plan
sumPrim t q@(ValueVector _) = vecSum t q
sumPrim _ _ = $impossible

sumLift :: VectorAlgebra a =>  Plan -> Graph a Plan
sumLift (NestedVector d1 vs1@(ValueVector _)) = vecSumLift (DescrVector d1) vs1 
sumLift _ = $impossible

distL :: VectorAlgebra a => Plan -> Plan -> Graph a Plan
distL q1@(ValueVector _) (NestedVector d vs) = do
                                                o <- outer vs
                                                (v, _) <- distLift q1 o
                                                return $ attachV (DescrVector d) v
distL (NestedVector d1 vs1) (NestedVector d2 vs2) = do 
                                                     o <- outer vs2
                                                     (d, p) <- distLift (DescrVector d1) o
                                                     e3 <- chainRenameFilter p vs1
                                                     return $ attachV (DescrVector d2) $ attachV d e3
distL (AClosure n v i xs x f fl) q2 = do
                                        v' <- distL v q2
                                        xs' <- mapEnv (\y -> distL y v') xs
                                        return $ AClosure n v' (i + 1) xs' x f fl
distL (PairVector e1 e1') e2 = PairVector <$> distL e1 e2 <*> distL e1' e2
distL e1 (PairVector e2 _) = distL e1 e2
distL _e1 _e2 = error $ "distL: Should not be possible" ++ show _e1 ++ "\n" ++ show _e2
-}
{-
ifList :: VectorAlgebra a => Plan -> Plan -> Plan -> Graph a Plan
{-ifList qb@(PrimVal _) (ValueVector lyt1 q1) (ValueVector lyt2 q2) =
    do
     d1' <- distPrim qb (DescrVector q1)  
     (d1, p1) <- restrictVec (DescrVector q1) d1'
     qb' <- notPrim qb
     d2' <- distPrim qb' (DescrVector q2)  
     (d2, p2) <- restrictVec (DescrVector q2) d2'
     r1 <- renameOuter p1 vs1
     r2 <- renameOuter p2 vs2
     e3 <- appendR r1 r2
     (d, _, _) <- append d1 d2
     return $ attachV d e3 -}
ifList (PrimVal _ qb) (PrimVal lyt1 q1) (PrimVal _ q2) = (\(DBV q _) -> ) <$> ifPrimList (DBP qb [1]) (DBV q1 $ snd $ projectFromPos lyt1) (DBV q2 $ snd $ projectFromPos lyt1)
-}
fstA :: VectorAlgebra a => Plan -> Graph a Plan   
fstA (PrimVal (Pair (Nest q lyt) _p2) _q) = return $ ValueVector lyt q
fstA (PrimVal p@(Pair p1 _p2) q) = do
                                     let (_, allCols) = projectFromPos p
                                     let (p1', cols) = projectFromPos p1
                                     (DBP proj _) <- projectA (DBP q allCols) cols
                                     return $ PrimVal p1' proj
fstA e1 = error $ "fstA: " ++ show e1                                                     

fstL :: VectorAlgebra a => Plan -> Graph a Plan   
fstL (ValueVector p@(Pair p1 _p2) q) = do
                                        let (_, allCols) = projectFromPos p
                                        let(p1', cols) = projectFromPos p1
                                        (DBV proj _) <- projectL (DBV q allCols) cols
                                        return $ ValueVector p1' proj

sndA :: VectorAlgebra a => Plan -> Graph a Plan   
sndA (PrimVal (Pair _p1 (Nest q lyt)) _q) = return $ ValueVector lyt q
sndA (PrimVal p@(Pair _p1 p2) q) = do
                                    let (_, allCols) = projectFromPos p
                                    let (p2', cols) = projectFromPos p2
                                    (DBP proj _) <- projectA (DBP q allCols) cols
                                    return $ PrimVal p2' proj
    
sndL :: VectorAlgebra a => Plan -> Graph a Plan   
sndL (ValueVector p@(Pair _p1 p2) q) = do
                                        let (_, allCols) = projectFromPos p
                                        let (p2', cols) = projectFromPos p2
                                        (DBV proj _) <- projectL (DBV q allCols) cols
                                        return $ ValueVector p2' proj


projectFromPos :: Layout AlgNode -> (Layout AlgNode, [DBCol])
projectFromPos = (\(x,y,_) -> (x,y)) . (projectFromPosWork 1)
    where
      projectFromPosWork :: Int -> Layout AlgNode -> (Layout AlgNode, [DBCol], Int)
      projectFromPosWork c (InColumn i)   = (InColumn c, [i], c + 1)
      projectFromPosWork c (Nest q l)       = (Nest q l, [], c)
      projectFromPosWork c (Pair p1 p2)   = let (p1', cols1, c') = projectFromPosWork c p1
                                                (p2', cols2, c'') = projectFromPosWork c' p2
                                             in (Pair p1' p2', cols1 ++ cols2, c'')