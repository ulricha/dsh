module Language.ParallelLang.VL.MetaPrimitives where

import Language.ParallelLang.VL.Data.Vector
import Language.ParallelLang.VL.Data.DBVector
import Language.ParallelLang.VL.VectorPrimitives

import Control.Applicative

fromLayout :: Layout a -> [DBCol]
fromLayout (InColumn i) = [i]
fromLayout (Nest _ _) = []
fromLayout (Pair l1 l2) = fromLayout l1 ++ fromLayout l2

-- | chainRenameFilter renames and filters a vector according to a propagation vector
-- and propagates these changes to all inner vectors. No reordering is applied,
-- that is the propagation vector must not change the order of tuples.
chainRenameFilter :: VectorAlgebra a => RenameVector -> Layout AlgNode -> Graph a (Layout AlgNode) 
chainRenameFilter _ l@(InColumn _) = return l
chainRenameFilter r (Nest q lyt) = do
                                    (DBV q' _, r') <- propFilter r (DBV q (fromLayout lyt))
                                    lyt' <- chainRenameFilter r' lyt
                                    return $ Nest q' lyt'
chainRenameFilter r (Pair l1 l2) = Pair <$> chainRenameFilter r l1 <*> chainRenameFilter r l2

-- | chainReorder renames and filters a vector according to a propagation vector
-- and propagates these changes to all inner vectors. The propagation vector
-- may change the order of tuples.
chainReorder :: VectorAlgebra a => PropVector -> Layout AlgNode -> Graph a (Layout AlgNode)
chainReorder _ l@(InColumn _) = return l
chainReorder p (Nest q lyt) = do
                                (DBV q' _, p') <- propReorder p (DBV q (fromLayout lyt))
                                lyt' <- chainReorder p' lyt
                                return $ Nest q' lyt'
chainReorder p (Pair l1 l2) = Pair <$> chainReorder p l1 <*> chainReorder p l2

-- | renameOuter renames and filters a vector according to a propagation vector
-- Changes are not propagated to inner vectors.
renameOuter :: VectorAlgebra a => RenameVector -> Plan -> Graph a Plan
renameOuter p (ValueVector lyt q) = ValueVector lyt . (\(DBV x _) -> x) <$> propRename p (DBV q (fromLayout lyt))
renameOuter _ _ = error "renameOuter: Not possible"

renameOuter' :: VectorAlgebra a => RenameVector -> Layout AlgNode -> Graph a (Layout AlgNode)
renameOuter' _ l@(InColumn _) = return l
renameOuter' r (Nest q lyt) = flip Nest lyt . (\(DBV x _) -> x) <$> propRename r (DBV q (fromLayout lyt))
renameOuter' r (Pair l1 l2) = Pair <$> renameOuter' r l1 <*> renameOuter' r l2
                                
-- | Append two vectors
appendR :: VectorAlgebra a => Plan -> Plan -> Graph a Plan
appendR (ValueVector lyt1 q1) (ValueVector lyt2 q2) = do
                                                        (DBV v _, p1, p2) <- append (DBV q1 (fromLayout lyt1)) (DBV q2 (fromLayout lyt2))
                                                        lyt1' <- renameOuter' p1 lyt1
                                                        lyt2' <- renameOuter' p2 lyt2
                                                        lyt' <- appendR' lyt1' lyt2'
                                                        return $ ValueVector lyt' v
appendR _ _ = error "appendR: Should not be possible"

appendR' :: VectorAlgebra a => Layout AlgNode -> Layout AlgNode -> Graph a (Layout AlgNode)
appendR' (InColumn i1) (InColumn i2) | i1 == i2 = return $ InColumn i1
                                     | otherwise = error "appendR': Incompatible vectors"
appendR' (Nest q1 lyt1) (Nest q2 lyt2) = (\(ValueVector lyt q) -> Nest q lyt) <$> appendR (ValueVector lyt1 q1) (ValueVector lyt2 q2)
appendR' (Pair ll1 lr1) (Pair ll2 lr2) = Pair <$> appendR' ll1 ll2 <*> appendR' lr1 lr2
appendR' _ _ = error "appendR': Should not be possible"
