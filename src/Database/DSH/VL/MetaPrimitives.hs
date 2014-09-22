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
fromLayout (LCol i)    = [i]
fromLayout (LNest _ _) = []
fromLayout (LTuple ls) = concatMap fromLayout ls

-- | chainRenameFilter renames and filters a vector according to a rename vector
-- and propagates these changes to all inner vectors. No reordering is applied,
-- that is the propagation vector must not change the order of tuples.
chainRenameFilter :: RVec -> Layout VLDVec -> Build VL (Layout VLDVec)
chainRenameFilter _ l@(LCol _) = return l
chainRenameFilter r (LNest q lyt) = do
    (q', r') <- vlPropFilter r q
    lyt'     <- chainRenameFilter r' lyt
    return $ LNest q' lyt'
chainRenameFilter r (LTuple lyts) = LTuple <$> mapM (chainRenameFilter r) lyts
    
-- | chainReorder renames and filters a vector according to a propagation vector
-- and propagates these changes to all inner vectors. The propagation vector
-- may change the order of tuples.
chainReorder :: PVec -> Layout VLDVec -> Build VL (Layout VLDVec)
chainReorder _ l@(LCol _) = return l
chainReorder p (LNest q lyt) = do
    (q', p') <- vlPropReorder p q
    lyt'     <- chainReorder p' lyt
    return $ LNest q' lyt'
chainReorder p (LTuple lyts) = LTuple <$> mapM (chainReorder p) lyts

-- | renameOuter renames and filters a vector according to a rename
-- vector. Changes are not propagated to inner vectors.
renameOuter :: RVec -> Shape VLDVec -> Build VL (Shape VLDVec)
renameOuter p (VShape q lyt) = flip VShape lyt <$> vlPropRename p q
renameOuter _ _ = error "renameOuter: Not possible"

renameOuter' :: RVec -> Layout VLDVec -> Build VL (Layout VLDVec)
renameOuter' _ l@(LCol _)    = return l
renameOuter' r (LNest q lyt) = flip LNest lyt <$> vlPropRename r q
renameOuter' r (LTuple lyts)   = LTuple <$> mapM (renameOuter' r) lyts

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
appendLayout (LTuple lyts1) (LTuple lyts2) =
    LTuple <$> (mapM (uncurry appendLayout) $ zip lyts1 lyts2)
appendLayout _ _ = $impossible
