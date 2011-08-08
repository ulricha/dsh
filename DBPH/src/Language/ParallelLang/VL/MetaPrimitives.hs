module Language.ParallelLang.VL.MetaPrimitives where

import Language.ParallelLang.VL.Algebra
import Language.ParallelLang.VL.Data.Query
import Language.ParallelLang.VL.VectorPrimitives

chainPropagate :: VectorAlgebra a => Plan -> Plan -> Graph a Plan
chainPropagate p q@(ValueVector _) = do 
                                      TupleVector [v, _] <- propagateIn p q
                                      return v
chainPropagate p (NestedVector d vs) = do
                                        TupleVector [v', p'] <- propagateIn p (DescrVector d)
                                        e3 <- chainPropagate p' vs
                                        return $ attachV v' e3
chainPropagate _ _ = error "chainPropagate: Should not be possible"

-- | Append two vectors
appendR :: VectorAlgebra a => Plan -> Plan -> Graph a Plan
appendR e1@(ValueVector _) e2@(ValueVector _)
                    = do
                          TupleVector [v, _, _] <- append e1 e2
                          return v
appendR (NestedVector d1 vs1) (NestedVector d2 vs2)
                    = do
                        TupleVector [v, p1, p2] <- append (DescrVector d1) (DescrVector d2)
                        e1' <- renameOuter p1 vs1
                        e2' <- renameOuter p2 vs2
                        e3 <- appendR e1' e2'
                        return $ attachV v e3
appendR _ _ = error "appendR: Should not be possible"

-- | Apply renaming to the outermost vector
renameOuter :: VectorAlgebra a => Plan -> Plan -> Graph a Plan
renameOuter p@(PropVector _) e@(ValueVector _)
                                = rename p e
renameOuter p@(PropVector _) (NestedVector h t)
                                = do
                                    d <- rename p (DescrVector h)
                                    return $ attachV d t
renameOuter _ _ = error "renameOuter: Should not be possible"

isNestListM :: VectorAlgebra a => Plan -> Plan -> Plan -> Graph a Plan
isNestListM qb@(PrimVal _) (NestedVector q1 vs1) (NestedVector q2 vs2) =
    do
     d1' <- distPrim qb (DescrVector q1)  
     TupleVector [d1, p1] <- restrictVec (DescrVector q1) d1'
     d2' <- distPrim qb (DescrVector q2)  
     TupleVector [d2, p2] <- restrictVec (DescrVector q2) d2'
     r1 <- renameOuter p1 vs1
     r2 <- renameOuter p2 vs2
     e3 <- appendR r1 r2
     TupleVector [d, _, _] <- append d1 d2
     return $ attachV d e3
isNestListM _ _ _ = error "isNestList: Should not be possible"
