{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

-- | This module defines the kinds of vectors that occur in VL
-- programs.
module Database.DSH.Common.Vector
    ( DBCol
    , DagVector
    , vectorNodes
    , updateVector
    , ADVec(..)
    , VLDVec(..)
    , NDVec
    , PVec(..)
    , RVec(..)
    ) where

import           Data.Aeson.TH

import           Database.Algebra.Dag.Common

import           Database.DSH.VL.Lang

-- | Common properties of data vectors
class DagVector v where
    -- | Return all graph nodes which represent the vector.
    vectorNodes :: v -> [AlgNode]

    -- | Replace a node in the vector
    updateVector :: AlgNode -> AlgNode -> v -> v

-- | Data vectors. A data vector references a result in an algebra DAG
-- and stores the number of payload columns that it has. 'ADVec'
-- abstracts over the type of references into the graph.
data ADVec r = ADVec r [DBCol]
    deriving (Show, Read)

-- | Data vectors that reference single nodes in an algebra graph
-- (used for table algebra and X100 with an n-ary storage model).
type NDVec = ADVec AlgNode

instance DagVector NDVec where
    vectorNodes (ADVec q _) = [q]

    updateVector n1 n2 (ADVec q cols)
        | q == n1   = ADVec n2 cols
        | otherwise = ADVec q cols

-- | A VL data vector references an operator in a VL DAG.
newtype VLDVec = VLDVec AlgNode
    deriving (Show, Read)

instance DagVector VLDVec where
    vectorNodes (VLDVec q) = [q]

    updateVector n1 n2 (VLDVec q)
        | q == n1   = VLDVec n2
        | otherwise = VLDVec q


-- | Propagation vectors. A @PVec@ simply references a node in an
-- algebra Dag.
data PVec = PVec AlgNode

-- | Rename vectors. A @RVec@ simply references a node in an algebra
-- Dag.
data RVec = RVec AlgNode

$(deriveJSON defaultOptions ''ADVec)
$(deriveJSON defaultOptions ''PVec)
$(deriveJSON defaultOptions ''RVec)
$(deriveJSON defaultOptions ''VLDVec)
