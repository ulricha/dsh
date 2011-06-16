module Language.ParallelLang.VL.VectorOperations where

import Language.ParallelLang.VL.Algebra
import Language.ParallelLang.VL.Data.Query
import Language.ParallelLang.VL.VectorPrimitives
import Language.ParallelLang.VL.MetaPrimitives

import Control.Applicative


lengthLift :: Plan -> Graph Plan
lengthLift (NestedVector d vs1) = do 
                                   v <- outer vs1
                                   ls <- lengthSeg v
                                   return (NestedVector d ls)

lengthV :: Plan -> Graph Plan
lengthV v = do
             v' <- outer v
             lengthA v'

consEmpty :: Plan -> Graph Plan
consEmpty q@(PrimVal _) = singletonPrim q -- Corresponds to rule [cons-empty-1]
consEmpty q | nestingDepth q > 0 = singletonVec q
            | otherwise = error "consEmpty: Can't construct consEmpty node"

cons :: Plan -> Plan -> Graph Plan
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

consLift :: Plan -> Plan -> Graph Plan
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

restrict :: Plan -> Plan -> Graph Plan
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

combine :: Plan -> Plan -> Plan -> Graph Plan
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

bPermute :: Plan -> Plan -> Graph Plan
bPermute e1 e2 | nestingDepth e1 == 1 && nestingDepth e2 == 1
                    = do
                        TupleVector [v, _] <- bPermuteVec e1 e2
                        return v
               | otherwise = error "bPermute: Can't construct bPermute node"

dist :: Plan -> Plan -> Graph Plan
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
                                                        TupleVector [d, p] <- distDesc o1 o2
                                                        et <- extract q1 1
                                                        e3 <- chainPropagate p et
                                                        o <- outer q2
                                                        return $ attachV o $ attachV d e3
                              | otherwise           = error "dist: Not a list vector"
dist q1@(Closure n env x f fl) q2 | nestingDepth q2 > 0 = (\env' -> AClosure n q2 1 env' x f fl) <$> mapEnv (flip dist q2) env

mapEnv :: (Plan -> Graph Plan) -> [(String, Plan)] -> Graph [(String, Plan)]
mapEnv f ((x, p):xs) = (\p' xs' -> (x, p'):xs') <$> f p <*> mapEnv f xs
mapEnv f []          = return []



distL :: Plan -> Plan -> Graph (Plan)
distL q1@(ValueVector _) (NestedVector d vs) = do
                                                o <- outer vs
                                                TupleVector [v, _] <- distLift q1 o
                                                return $ attachV (DescrVector d) v
distL (NestedVector d1 vs1) (NestedVector d2 vs2) = do 
                                                     o <- outer vs2
                                                     TupleVector [d, p] <- distLift (DescrVector d1) o
                                                     e3 <- chainPropagate p vs1
                                                     return $ attachV (DescrVector d2) $ attachV d e3
distL (AClosure n v i xs x f fl) q2 = do
                                        v' <- dist q2 v
                                        xs' <- mapEnv (\x -> distL x v') xs
                                        return $ AClosure n v' (i + 1) xs' x f fl


