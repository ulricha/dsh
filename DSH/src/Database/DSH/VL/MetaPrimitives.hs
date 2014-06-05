{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.VL.MetaPrimitives where

import           Control.Applicative

import           Database.Algebra.Dag.Build

import           Database.DSH.Impossible
import           Database.DSH.VL.Vector
import           Database.DSH.VL.Shape
import           Database.DSH.VL.Lang             (VL ())
import           Database.DSH.VL.VLPrimitives


fromLayout :: Layout -> [DBCol]
fromLayout (InColumn i) = [i]
fromLayout (Nest _ _) = []
fromLayout (Pair l1 l2) = fromLayout l1 ++ fromLayout l2

-- | chainRenameFilter renames and filters a vector according to a rename vector
-- and propagates these changes to all inner vectors. No reordering is applied,
-- that is the propagation vector must not change the order of tuples.
chainRenameFilter :: RVec -> Layout -> Build VL Layout
chainRenameFilter _ l@(InColumn _) = return l
chainRenameFilter r (Nest q lyt) = do
    (q', r') <- vlPropFilter r q
    lyt'     <- chainRenameFilter r' lyt
    return $ Nest q' lyt'
chainRenameFilter r (Pair l1 l2) =
    Pair <$> chainRenameFilter r l1 <*> chainRenameFilter r l2

-- | chainReorder renames and filters a vector according to a propagation vector
-- and propagates these changes to all inner vectors. The propagation vector
-- may change the order of tuples.
chainReorder :: PVec -> Layout -> Build VL Layout
chainReorder _ l@(InColumn _) = return l
chainReorder p (Nest q lyt) = do
    (q', p') <- vlPropReorder p q
    lyt' <- chainReorder p' lyt
    return $ Nest q' lyt'
chainReorder p (Pair l1 l2) =
    Pair <$> chainReorder p l1 <*> chainReorder p l2

-- | renameOuter renames and filters a vector according to a rename
-- vector. Changes are not propagated to inner vectors.
renameOuter :: RVec -> Shape -> Build VL Shape
renameOuter p (ValueVector q lyt) = flip ValueVector lyt <$> vlPropRename p q
renameOuter _ _ = error "renameOuter: Not possible"

renameOuter' :: RVec -> Layout -> Build VL Layout
renameOuter' _ l@(InColumn _) = return l
renameOuter' r (Nest q lyt)   = flip Nest lyt <$> vlPropRename r q
renameOuter' r (Pair l1 l2)   = Pair <$> renameOuter' r l1 <*> renameOuter' r l2

-- | Append two inner vectors (segment-wise).
appendInnerVec :: Shape -> Shape -> Build VL Shape
appendInnerVec (ValueVector q1 lyt1) (ValueVector q2 lyt2) = do
    -- Append the current vectors
    (v, p1, p2) <- vlAppendS q1 q2
    -- Propagate position changes to descriptors of any inner vectors
    lyt1'       <- renameOuter' p1 lyt1
    lyt2'       <- renameOuter' p2 lyt2
    -- Append the layouts, i.e. actually append all inner vectors
    lyt'        <- appendLayout lyt1' lyt2'
    return $ ValueVector v lyt'
appendInnerVec _ _ = $impossible

-- | Append two (outer) vectors regularly.
appendVec :: Shape -> Shape -> Build VL Shape
appendVec (ValueVector q1 lyt1) (ValueVector q2 lyt2) = do
    -- Append the current vectors
    (v, p1, p2) <- vlAppend q1 q2
    -- Propagate position changes to descriptors of any inner vectors
    lyt1'       <- renameOuter' p1 lyt1
    lyt2'       <- renameOuter' p2 lyt2
    -- Append the layouts, i.e. actually append all inner vectors
    lyt'        <- appendLayout lyt1' lyt2'
    return $ ValueVector v lyt'
appendVec _ _ = $impossible

-- | Traverse a layout and append all nested vectors that are
-- encountered.
appendLayout :: Layout -> Layout -> Build VL Layout
appendLayout (InColumn i1) (InColumn i2)
    | i1 == i2  = return $ InColumn i1
    | otherwise = error "appendR': Incompatible vectors"
-- Append two nested vectors
appendLayout (Nest q1 lyt1) (Nest q2 lyt2) = do
    a <- appendInnerVec (ValueVector q1 lyt1) (ValueVector q2 lyt2)
    case a of
        ValueVector q lyt -> return $ Nest q lyt
        _                 -> $impossible
appendLayout (Pair ll1 lr1) (Pair ll2 lr2) =
    Pair <$> appendLayout ll1 ll2 <*> appendLayout lr1 lr2
appendLayout _ _ = $impossible
