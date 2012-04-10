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
                    
concatLift :: VectorAlgebra a => Plan -> Graph a Plan
concatLift (NestedVector d (NestedVector d' vs)) = do
                                                    p <- descToRename (DescrVector d')
                                                    vs' <- renameOuter p vs
                                                    return $ NestedVector d vs'
concatLift _ = error "concatLift: Should not be possible"

lengthLift :: VectorAlgebra a => Plan -> Graph a Plan
lengthLift (PairVector e1 _e2) = lengthLift e1
lengthLift (NestedVector d vs1) = do 
                                   v <- outer vs1
                                   ls <- lengthSeg (DescrVector d) v
                                   p <- descToRename (DescrVector d)
                                   propRename p ls
lengthLift _ = error "lengthLift: Should not be possible"

lengthV :: VectorAlgebra a => Plan -> Graph a Plan
lengthV (PairVector e1 _e2) = lengthV e1
lengthV v = do
             v' <- outer v
             lengthA v'

consEmpty :: VectorAlgebra a => Plan -> Graph a Plan
consEmpty q@(PrimVal _) = singletonPrim q -- Corresponds to rule [cons-empty-1]
consEmpty q | nestingDepth q > 0 = singletonVec q
            | otherwise = error "consEmpty: Can't construct consEmpty node"
-}

cons :: VectorAlgebra a => Plan -> Plan -> Graph a Plan
cons = undefined
{-
cons q1@(PrimVal l1 _) (ValueVector l2 q2) = do
                                            n <- singleTonPrim q1
                                            (v, _, _) <- append n q2

cons (PrimVal  )
cons (PairVector x y) (PairVector xs ys) = do
                                                    xxs <- cons x xs
                                                    yys <- cons y ys
                                                    return $ PairVector xxs yys
cons q1@(PrimVal _) q2@(ValueVector _)
                -- corresponds to rule [cons-1]
                = do
                    n <- singletonPrim q1
                    (v, _, _) <- append n q2
                    return v
cons q1 q2@(NestedVector d2 vs2) | nestingDepth q1 > 0 && nestingDepth q2 == (nestingDepth q1) + 1
                -- Corresponds to rule [cons-2]
                = do
                    o <- (singletonVec q1) >>= outer
                    (v, p1, p2) <- append o (DescrVector d2)
                    r1 <- renameOuter p1 q1
                    r2 <- renameOuter p2 vs2
                    e3 <- appendR r1 r2
                    return $ attachV v e3
            | otherwise = error "cons: Can't construct cons node"
cons q1 q2 = error $ "cons: Should not be possible" ++ show q1 ++ "*******" ++ show q2
-}
{-
consLift :: VectorAlgebra a => Plan -> Plan -> Graph a Plan
consLift e1@(ValueVector _) e2@(NestedVector d2 vs2) | nestingDepth e2 == 2
                      -- Case that e1 has a nesting depth of 1
                    = do
                        s <- segment e1
                        (v, _, _) <- append s vs2
                        return $ attachV (DescrVector d2) v
consLift e1@(NestedVector d1 vs1) e2@(NestedVector d2 vs2) 
               | nestingDepth e1 > 1 && nestingDepth e2 == (nestingDepth e1) + 1
                      -- Case that e1 has a nesting depth > 1
                    = do
                        s <- segment (DescrVector d1)
                        o <- outer vs2
                        (v, p1, p2) <- append s o
                        r1 <- renameOuter p1 vs1
                        vs2' <- concatV vs2 
                        r2 <- renameOuter p2 vs2'
                        e3 <- appendR r1 r2
                        return $ attachV (DescrVector d2) $ attachV v e3
               | otherwise = error "consLift: Can't construct consLift node"
consLift (PairVector x y) (PairVector xs ys) = do
                                                        xxs <- consLift x xs
                                                        yys <- consLift y ys
                                                        return $ PairVector xxs yys
consLift e1 e2 = error $ "consLift: Should not be possible: \n" ++ show e1 ++ " : " ++ show e2 

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
                           (v, p) <- distPrim (DBP q $ snd $ projectFromPos lyt) o
                           return undefined
{-
dist :: VectorAlgebra a => Plan -> Plan -> Graph a Plan
dist (PairVector e1 e2) q2 = do
                                 e1' <- dist e1 q2
                                 e2' <- dist e2 q2
                                 return $ PairVector e1' e2'
dist q1             (PairVector q2 _) = dist q1 q2
dist q1@(PrimVal _) q2        | nestingDepth q2 > 0 = do
                                                        o <- outer q2
                                                        distPrim q1 o
                              | otherwise           = error "dist: Not a list vector"
dist q1@(ValueVector _) q2    | nestingDepth q2 > 0 = do
                                                       d2v <- outer q2
                                                       (q1v, _) <- distDesc q1 d2v
                                                       return $ attachV d2v q1v
                              | otherwise           = error "dist: Not a list vector"
dist q1@(NestedVector _ _) q2 | nestingDepth q2 > 0 = do
                                                        o1 <- outer q1
                                                        o2 <- outer q2
                                                        (d, p) <- distDesc o1 o2
                                                        et <- concatV q1
                                                        e3 <- chainRenameFilter p et
                                                        o <- outer q2
                                                        return $ attachV o $ attachV d e3
                              | otherwise           = error "dist: Not a list vector"
dist (Closure n env x f fl) q2 | nestingDepth q2 > 0 = (\env' -> AClosure n q2 1 env' x f fl) <$> mapEnv (flip dist q2) env
dist e1 e2 = error $ "dist: Should not be possible" ++ show e1 ++ " " ++ show e2

mapEnv :: VectorAlgebra a => (Plan -> Graph a Plan) -> [(String, Plan)] -> Graph a [(String, Plan)]
mapEnv f  ((x, p):xs) = (\p' xs' -> (x, p'):xs') <$> f p <*> mapEnv f xs
mapEnv _f []          = return []

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

ifList :: VectorAlgebra a => Plan -> Plan -> Plan -> Graph a Plan
ifList qb (PairVector e11 e12) (PairVector e21 e22) = do
                                                                e1 <- ifList qb e11 e21
                                                                e2 <- ifList qb e12 e22
                                                                return $ PairVector e1 e2
ifList qb@(PrimVal _) (NestedVector q1 vs1) (NestedVector q2 vs2) =
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
     return $ attachV d e3
ifList qb e1 e2 = ifPrimList qb e1 e2
-}

fstA :: VectorAlgebra a => Plan -> Graph a Plan   
fstA (PrimVal p@(Pair p1 _p2) q) = do
                                     let (_, allCols) = projectFromPos p
                                     let (p1', cols) = projectFromPos p1
                                     (DBP proj _) <- projectA (DBP q allCols) cols
                                     return $ PrimVal p1' proj
                                                    
fstL :: VectorAlgebra a => Plan -> Graph a Plan   
fstL (ValueVector p@(Pair p1 _p2) q) = do
                                        let (_, allCols) = projectFromPos p
                                        let(p1', cols) = projectFromPos p1
                                        (DBV proj _) <- projectL (DBV q allCols) cols
                                        return $ ValueVector p1' proj

sndA :: VectorAlgebra a => Plan -> Graph a Plan   
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