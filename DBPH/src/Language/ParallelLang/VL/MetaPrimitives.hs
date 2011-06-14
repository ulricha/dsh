module Language.ParallelLang.VL.MetaPrimitives where

import Language.ParallelLang.VL.Algebra
import Language.ParallelLang.VL.Data.Query
import Language.ParallelLang.VL.VectorPrimitives

chainPropagate :: Plan -> Plan -> Graph Plan
chainPropagate p q@(ValueVector _) = do 
                                      TupleVector [v, _] <- propagateIn p q
                                      return v
chainPropagate p (NestedVector d vs) = do
                                        TupleVector [v', p'] <- propagateIn p (DescrVector d)
                                        e3 <- chainPropagate p' vs
                                        return $ attachV v' e3


-- | Append two vectors
appendR :: Plan -> Plan -> Graph Plan
appendR e1@(ValueVector _) e2@(ValueVector _)
                    = do
                          TupleVector [v, _, _] <- append e1 e2
                          return v
appendR e1@(NestedVector d1 vs1) e2@(NestedVector d2 vs2)
                    = do
                        TupleVector [v, p1, p2] <- append (DescrVector d1) (DescrVector d2)
                        e1' <- renameOuter p1 vs1
                        e2' <- renameOuter p2 vs2
                        e3 <- appendR e1' e2'
                        return $ attachV v e3

-- | Apply renaming to the outermost vector
renameOuter :: Plan -> Plan -> Graph Plan
renameOuter p@(PropVector _) e@(ValueVector _)
                                = rename p e
renameOuter p@(PropVector _) e@(NestedVector h t)
                                = do
                                    d <- rename p (DescrVector h)
                                    return $ attachV d t


