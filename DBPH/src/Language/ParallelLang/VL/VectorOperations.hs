module Language.ParallelLang.VL.VectorOperations where

import Language.ParallelLang.VL.Algebra
import Language.ParallelLang.VL.Data.Query
import Language.ParallelLang.VL.VectorPrimitives
import Language.ParallelLang.VL.MetaPrimitives

import Control.Applicative

groupByS :: VectorAlgebra a => Plan -> Plan -> Graph a Plan
groupByS e1 e2@(ValueVector _) = do
                                  TupleVector [d, v, _] <- groupBy e1 e2
                                  return $ attachV d v
groupByS e1 (NestedVector d2 vs2) = do
                                     TupleVector [d, v, p] <- groupBy e1 (DescrVector d2)
                                     vs' <- chainPropagate p vs2
                                     return $ attachV d $ attachV v vs'
groupByS e1 (TupleVector es) = TupleVector <$> mapM (groupByS e1) es
groupByS _e1 _e2 = error $ "groupByS: Should not be possible " ++ show _e1 ++ "\n" ++ show _e2

groupByL :: VectorAlgebra a => Plan -> Plan -> Graph a Plan
groupByL (NestedVector _d1 v1@(ValueVector _)) (NestedVector d2 v2@(ValueVector _)) = do
                                  TupleVector [d, v, _] <- groupBy v1 v2
                                  return $ attachV (DescrVector d2) $ attachV d v
groupByL (NestedVector _d1 v1@(ValueVector _)) (NestedVector d2 (NestedVector d' vs2)) = do
                                     TupleVector [d, v, p] <- groupBy v1 (DescrVector d')
                                     vs' <- chainPropagate p vs2
                                     return $ attachV (DescrVector d2) $ attachV d $ attachV v vs'
groupByL e1 (TupleVector es) = TupleVector <$> mapM (groupByL e1) es
groupByL _ _ = error "groupByL: Should not be possible"
                    
concatLift :: VectorAlgebra a => Plan -> Graph a Plan
concatLift (NestedVector d (NestedVector d' vs)) = do
                                                    p <- descToProp (DescrVector d')
                                                    vs' <- renameOuter p vs
                                                    return $ NestedVector d vs'
concatLift _ = error "concatLift: Should not be possible"

lengthLift :: VectorAlgebra a => Plan -> Graph a Plan
lengthLift (NestedVector d vs1) = do 
                                   v <- outer vs1
                                   ls <- lengthSeg (DescrVector d) v
                                   p <- descToProp (DescrVector d)
                                   rename p ls
lengthLift _ = error "lengthLift: Should not be possible"

lengthV :: VectorAlgebra a => Plan -> Graph a Plan
lengthV v = do
             v' <- outer v
             lengthA v'

consEmpty :: VectorAlgebra a => Plan -> Graph a Plan
consEmpty q@(PrimVal _) = singletonPrim q -- Corresponds to rule [cons-empty-1]
consEmpty q | nestingDepth q > 0 = singletonVec q
            | otherwise = error "consEmpty: Can't construct consEmpty node"

cons :: VectorAlgebra a => Plan -> Plan -> Graph a Plan
cons q1@(PrimVal _) q2@(ValueVector _)
                -- corresponds to rule [cons-1]
                = do
                    n <- singletonPrim q1
                    TupleVector [v, _, _] <- append n q2
                    return v
cons q1 q2@(NestedVector d2 vs2) | nestingDepth q1 > 0 && nestingDepth q2 == (nestingDepth q1) + 1
                -- Corresponds to rule [cons-2]
                = do
                    o <- (singletonVec q1) >>= outer
                    TupleVector [v, p1, p2] <- append o (DescrVector d2)
                    r1 <- renameOuter p1 q1
                    r2 <- renameOuter p2 vs2
                    e3 <- appendR r1 r2
                    return $ attachV v e3
            | otherwise = error "cons: Can't construct cons node"
cons q1 q2 = error $ "cons: Should not be possible" ++ show q1 ++ "*******" ++ show q2

consLift :: VectorAlgebra a => Plan -> Plan -> Graph a Plan
consLift e1@(ValueVector _) e2@(NestedVector d2 vs2) | nestingDepth e2 == 2
                      -- Case that e1 has a nesting depth of 1
                    = do
                        s <- segment e1
                        TupleVector [v, _, _] <- append s vs2
                        return $ attachV (DescrVector d2) v
consLift e1@(NestedVector d1 vs1) e2@(NestedVector d2 vs2) 
               | nestingDepth e1 > 1 && nestingDepth e2 == (nestingDepth e1) + 1
                      -- Case that e1 has a nesting depth > 1
                    = do
                        s <- segment (DescrVector d1)
                        o <- outer vs2
                        TupleVector [v, p1, p2] <- append s o
                        r1 <- renameOuter p1 vs1
                        vs2' <- extract vs2 1
                        r2 <- renameOuter p2 vs2'
                        e3 <- appendR r1 r2
                        return $ attachV (DescrVector d2) $ attachV v e3
               | otherwise = error "consLift: Can't construct consLift node"
consLift _ _ = error "consLift: Should not be possible"

restrict :: VectorAlgebra a => Plan -> Plan -> Graph a Plan
restrict e1@(ValueVector _) e2@(ValueVector _) 
                     -- Corresponds to compilation rule [restrict-1]
                   = do
                        TupleVector [v, _] <- restrictVec e1 e2
                        return v

restrict (NestedVector d1 vs1) e2@(ValueVector _)
                     -- Corresponds to compilation rule [restrict-2]
                   = do
                       TupleVector [v, p] <- restrictVec (DescrVector d1) e2
                       e3 <- chainPropagate p vs1
                       return $ attachV v e3
restrict e1 e2 = error $ "restrict: Can't construct restrict node " ++ show e1 ++ " " ++ show e2

combine :: VectorAlgebra a => Plan -> Plan -> Plan -> Graph a Plan
combine eb e1 e2 | nestingDepth eb == 1 && nestingDepth e1 == 1 && nestingDepth e2 == 1
                      -- Corresponds to compilation rule [combine-1]
                    = do
                        TupleVector [v, _, _] <- combineVec eb e1 e2
                        return v
                 | nestingDepth eb == 1 && nestingDepth e1 > 1 && nestingDepth e1 == nestingDepth e2
                      -- Corresponds to compilation rule [combine-2]
                    = do
                        let (NestedVector d1 vs1) = e1
                        let (NestedVector d2 vs2) = e2
                        TupleVector [v, p1, p2] <- combineVec eb (DescrVector d1) (DescrVector d2)
                        r1 <- renameOuter p1 vs1
                        r2 <- renameOuter p2 vs2
                        e3 <- appendR r1 r2
                        return $ attachV v e3
                 | otherwise = error "combine: Can't construct combine node"

bPermute :: VectorAlgebra a => Plan -> Plan -> Graph a Plan
bPermute e1 e2 | nestingDepth e1 == 1 && nestingDepth e2 == 1
                    = do
                        TupleVector [v, _] <- bPermuteVec e1 e2
                        return v
               | otherwise = error "bPermute: Can't construct bPermute node"

dist :: VectorAlgebra a => Plan -> Plan -> Graph a Plan
dist q1             (TupleVector (q2:_)) = dist q1 q2
dist q1@(PrimVal _) q2        | nestingDepth q2 > 0 = do
                                                        o <- outer q2
                                                        distPrim q1 o
                              | otherwise           = error "dist: Not a list vector"
dist q1@(ValueVector _) q2    | nestingDepth q2 > 0 = do
                                                       d2v <- outer q2
                                                       TupleVector [q1v, _] <- distDesc q1 d2v
                                                       return $ attachV d2v q1v
                              | otherwise           = error "dist: Not a list vector"
dist q1@(NestedVector _ _) q2 | nestingDepth q2 > 0 = do
                                                        o1 <- outer q1
                                                        o2 <- outer q2
                                                        TupleVector [d, p@(PropVector _)] <- distDesc o1 o2
                                                        et <- extract q1 1
                                                        e3 <- chainPropagate p et
                                                        o <- outer q2
                                                        return $ attachV o $ attachV d e3
                              | otherwise           = error "dist: Not a list vector"
dist (Closure n env x f fl) q2 | nestingDepth q2 > 0 = (\env' -> AClosure n q2 1 env' x f fl) <$> mapEnv (flip dist q2) env
dist _ _ = error "dist: Should not be possible"

mapEnv :: VectorAlgebra a => (Plan -> Graph a Plan) -> [(String, Plan)] -> Graph a [(String, Plan)]
mapEnv f  ((x, p):xs) = (\p' xs' -> (x, p'):xs') <$> f p <*> mapEnv f xs
mapEnv _f []          = return []



distL :: VectorAlgebra a => Plan -> Plan -> Graph a Plan
distL q1@(ValueVector _) (NestedVector d vs) = do
                                                o <- outer vs
                                                TupleVector [v, _] <- distLift q1 o
                                                return $ attachV (DescrVector d) v
distL (NestedVector d1 vs1) (NestedVector d2 vs2) = do 
                                                     o <- outer vs2
                                                     TupleVector [d, p@(PropVector _)] <- distLift (DescrVector d1) o
                                                     e3 <- chainPropagate p vs1
                                                     return $ attachV (DescrVector d2) $ attachV d e3
distL (AClosure n v i xs x f fl) q2 = do
                                        v' <- distL q2 v
                                        xs' <- mapEnv (\y -> distL y v') xs
                                        return $ AClosure n v' (i + 1) xs' x f fl
distL _ _ = error "distL: Should not be possible"