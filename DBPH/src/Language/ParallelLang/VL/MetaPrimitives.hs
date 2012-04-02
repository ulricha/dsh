module Language.ParallelLang.VL.MetaPrimitives where

import Language.ParallelLang.VL.Algebra
import Language.ParallelLang.VL.Data.Query
import Language.ParallelLang.VL.VectorPrimitives

-- | chainRenameFilter renames and filters a vector according to a propagation vector
-- and propagates these changes to all inner vectors. No reordering is applied,
-- that is the propagation vector must not change the order of tuples.
chainRenameFilter :: VectorAlgebra a => RenameVector -> Plan -> Graph a Plan
chainRenameFilter p q@(ValueVector _) = do 
                                      (v, _) <- propFilter p q
                                      return v
chainRenameFilter p (NestedVector d vs) = do
                                        (v', p') <- propFilter p (DescrVector d)
                                        e3 <- chainRenameFilter p' vs
                                        return $ attachV v' e3
chainRenameFilter _ _ = error "chainRenameFilter: Should not be possible"
                  
-- | chainReorder renames and filters a vector according to a propagation vector
-- and propagates these changes to all inner vectors. The propagation vector
-- may change the order of tuples.
chainReorder :: VectorAlgebra a => PropVector -> Plan -> Graph a Plan
chainReorder p q@(ValueVector _) = do 
                                      (v, _) <- propReorder p q
                                      return v
chainReorder p (NestedVector d vs) = do
                                        (v', p') <- propReorder p (DescrVector d)
                                        e3 <- chainReorder p' vs
                                        return $ attachV v' e3
chainReorder _ _ = error "chainReorder: Should not be possible"
               
-- | renameOuter renames and filters a vector according to a propagation vector
-- Changes are not propagated to inner vectors.
renameOuter :: VectorAlgebra a => RenameVector -> Plan -> Graph a Plan
renameOuter p e@(ValueVector _)
                                = propRename p e
renameOuter p (NestedVector h t)
                                = do
                                    d <- propRename p (DescrVector h)
                                    return $ attachV d t
renameOuter _ _ = error "renameOuter: Should not be possible"

-- | Append two vectors
appendR :: VectorAlgebra a => Plan -> Plan -> Graph a Plan
appendR e1@(ValueVector _) e2@(ValueVector _)
                    = do
                          (v, _, _) <- append e1 e2
                          return v
appendR (NestedVector d1 vs1) (NestedVector d2 vs2)
                    = do
                        (v, p1, p2) <- append (DescrVector d1) (DescrVector d2)
                        e1' <- renameOuter p1 vs1
                        e2' <- renameOuter p2 vs2
                        e3 <- appendR e1' e2'
                        return $ attachV v e3
appendR _ _ = error "appendR: Should not be possible"

