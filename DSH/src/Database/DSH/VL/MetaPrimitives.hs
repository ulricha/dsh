module Database.DSH.VL.MetaPrimitives where

import Database.Algebra.VL.Data (VL())
import Database.DSH.VL.Data.GraphVector
import Database.DSH.VL.Data.DBVector
import Database.DSH.VL.VLPrimitives

import Control.Applicative

fromLayout :: Layout -> [DBCol]
fromLayout (InColumn i) = [i]
fromLayout (Nest _ _) = []
fromLayout (Pair l1 l2) = fromLayout l1 ++ fromLayout l2

-- | chainRenameFilter renames and filters a vector according to a propagation vector
-- and propagates these changes to all inner vectors. No reordering is applied,
-- that is the propagation vector must not change the order of tuples.
chainRenameFilter :: RenameVector -> Layout -> Graph VL Layout 
chainRenameFilter _ l@(InColumn _) = return l
chainRenameFilter r (Nest q lyt) = do
                                    (q', r') <- propFilter r q
                                    lyt' <- chainRenameFilter r' lyt
                                    return $ Nest q' lyt'
chainRenameFilter r (Pair l1 l2) = Pair <$> chainRenameFilter r l1 <*> chainRenameFilter r l2

-- | chainReorder renames and filters a vector according to a propagation vector
-- and propagates these changes to all inner vectors. The propagation vector
-- may change the order of tuples.
chainReorder :: PropVector -> Layout -> Graph VL Layout
chainReorder _ l@(InColumn _) = return l
chainReorder p (Nest q lyt) = do
                                (q', p') <- propReorder p q
                                lyt' <- chainReorder p' lyt
                                return $ Nest q' lyt'
chainReorder p (Pair l1 l2) = Pair <$> chainReorder p l1 <*> chainReorder p l2

-- | renameOuter renames and filters a vector according to a propagation vector
-- Changes are not propagated to inner vectors.
renameOuter :: RenameVector -> Shape -> Graph VL Shape
renameOuter p (ValueVector q lyt) = flip ValueVector lyt <$> propRename p q
renameOuter _ _ = error "renameOuter: Not possible"

renameOuter' :: RenameVector -> Layout -> Graph VL Layout
renameOuter' _ l@(InColumn _) = return l
renameOuter' r (Nest q lyt) = flip Nest lyt <$> propRename r q 
renameOuter' r (Pair l1 l2) = Pair <$> renameOuter' r l1 <*> renameOuter' r l2
                                
-- | Append two vectors
appendR :: Shape -> Shape -> Graph VL Shape
appendR (ValueVector q1 lyt1) (ValueVector q2 lyt2) = do
                                                        (v, p1, p2) <- append q1 q2
                                                        lyt1' <- renameOuter' p1 lyt1
                                                        lyt2' <- renameOuter' p2 lyt2
                                                        lyt' <- appendR' lyt1' lyt2'
                                                        return $ ValueVector v lyt'
appendR _ _ = error "appendR: Should not be possible"

appendR' :: Layout -> Layout -> Graph VL Layout
appendR' (InColumn i1) (InColumn i2) | i1 == i2 = return $ InColumn i1
                                     | otherwise = error "appendR': Incompatible vectors"
appendR' (Nest q1 lyt1) (Nest q2 lyt2) = (\(ValueVector q lyt) -> Nest q lyt) <$> appendR (ValueVector q1 lyt1) (ValueVector q2 lyt2)
appendR' (Pair ll1 lr1) (Pair ll2 lr2) = Pair <$> appendR' ll1 ll2 <*> appendR' lr1 lr2
appendR' _ _ = error "appendR': Should not be possible"
