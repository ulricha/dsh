{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.VL.MetaPrimitives where

import           Control.Applicative

import           Database.Algebra.Dag.Build

import           Database.DSH.Impossible
import           Database.DSH.VL.Vector
import           Database.DSH.Common.QueryPlan
import           Database.DSH.VL.Lang             (VL ())
import           Database.DSH.VL.VLPrimitives


fromLayout :: Layout VLDVec -> [DBCol]
fromLayout (LCol i)      = [i]
fromLayout (LNest _ _)   = []
fromLayout (LPair l1 l2) = fromLayout l1 ++ fromLayout l2

-- | chainRenameFilter renames and filters a vector according to a rename vector
-- and propagates these changes to all inner vectors. No reordering is applied,
-- that is the propagation vector must not change the order of tuples.
chainRenameFilter :: RVec -> Layout VLDVec -> Build VL (Layout VLDVec)
chainRenameFilter _ l@(LCol _) = return l
chainRenameFilter r (LNest q lyt) = do
    (q', r') <- vlPropFilter r q
    lyt'     <- chainRenameFilter r' lyt
    return $ LNest q' lyt'
chainRenameFilter r (LPair l1 l2) =
    LPair <$> chainRenameFilter r l1 <*> chainRenameFilter r l2

-- | chainReorder renames and filters a vector according to a propagation vector
-- and propagates these changes to all inner vectors. The propagation vector
-- may change the order of tuples.
chainReorder :: PVec -> Layout VLDVec -> Build VL (Layout VLDVec)
chainReorder _ l@(LCol _) = return l
chainReorder p (LNest q lyt) = do
    (q', p') <- vlPropReorder p q
    lyt'     <- chainReorder p' lyt
    return $ LNest q' lyt'
chainReorder p (LPair l1 l2) =
    LPair <$> chainReorder p l1 <*> chainReorder p l2

-- | renameOuter renames and filters a vector according to a rename
-- vector. Changes are not propagated to inner vectors.
renameOuter :: RVec -> Shape VLDVec -> Build VL (Shape VLDVec)
renameOuter p (VShape q lyt) = flip VShape lyt <$> vlPropRename p q
renameOuter _ _ = error "renameOuter: Not possible"

renameOuter' :: RVec -> Layout VLDVec -> Build VL (Layout VLDVec)
renameOuter' _ l@(LCol _)    = return l
renameOuter' r (LNest q lyt) = flip LNest lyt <$> vlPropRename r q
renameOuter' r (LPair l1 l2) = LPair <$> renameOuter' r l1 <*> renameOuter' r l2

-- | Append two inner vectors (segment-wise).
appendInnerVec :: Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
appendInnerVec (VShape q1 lyt1) (VShape q2 lyt2) = do
    -- Append the current vectors
    (v, p1, p2) <- vlAppendS q1 q2
    -- Propagate position changes to descriptors of any inner vectors
    lyt1'       <- renameOuter' p1 lyt1
    lyt2'       <- renameOuter' p2 lyt2
    -- Append the layouts, i.e. actually append all inner vectors
    lyt'        <- appendLayout lyt1' lyt2'
    return $ VShape v lyt'
appendInnerVec _ _ = $impossible

-- | Append two (outer) vectors regularly.
appendVec :: Shape VLDVec -> Shape VLDVec -> Build VL (Shape VLDVec)
appendVec (VShape q1 lyt1) (VShape q2 lyt2) = do
    -- Append the current vectors
    (v, p1, p2) <- vlAppend q1 q2
    -- Propagate position changes to descriptors of any inner vectors
    lyt1'       <- renameOuter' p1 lyt1
    lyt2'       <- renameOuter' p2 lyt2
    -- Append the layouts, i.e. actually append all inner vectors
    lyt'        <- appendLayout lyt1' lyt2'
    return $ VShape v lyt'
appendVec _ _ = $impossible

-- | Traverse a layout and append all nested vectors that are
-- encountered.
appendLayout :: Layout VLDVec -> Layout VLDVec -> Build VL (Layout VLDVec)
appendLayout (LCol i1) (LCol i2)
    | i1 == i2  = return $ LCol i1
    | otherwise = error "appendR': Incompatible vectors"
-- Append two nested vectors
appendLayout (LNest q1 lyt1) (LNest q2 lyt2) = do
    a <- appendInnerVec (VShape q1 lyt1) (VShape q2 lyt2)
    case a of
        VShape q lyt -> return $ LNest q lyt
        _            -> $impossible
appendLayout (LPair ll1 lr1) (LPair ll2 lr2) =
    LPair <$> appendLayout ll1 ll2 <*> appendLayout lr1 lr2
appendLayout _ _ = $impossible
