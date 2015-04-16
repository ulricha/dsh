{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- | This module defines the kinds of vectors that occur in VL
-- programs.
module Database.DSH.Common.Vector
    ( DBCol
    , ColName
    , RelationalVector(..)
    , DagVector
    , vectorNodes
    , updateVector
    , ADVec(..)
    , VLDVec(..)
    , NDVec
    , VLRVec(..)
    , VLKVec(..)
    , VLSVec(..)
    , VLFVec(..)
    ) where

import           Data.Aeson.TH
import qualified Data.Vector                 as V

import           Database.Algebra.Dag.Common

import           Database.DSH.VL.Lang

type ColName = String

--------------------------------------------------------------------------------
-- Abstractions over data vectors

-- | Concrete encodings of data vectors explicitly represent ordering
-- and segment information in relational columns.
class RelationalVector v where
    rvKeyCols :: v -> [ColName]
    rvItemCols :: v -> V.Vector ColName

-- | Common properties of data vectors that are represented by a DAG
-- plan of operators.
class DagVector v where
    -- | Return all graph nodes which represent the vector.
    vectorNodes :: v -> [AlgNode]

    -- | Replace a node in the vector
    updateVector :: AlgNode -> AlgNode -> v -> v

--------------------------------------------------------------------------------
-- Simple data vectors

-- | Data vectors. A data vector references a result in an algebra DAG
-- and stores the number of payload columns that it has. 'ADVec'
-- abstracts over the type of references into the graph.
data ADVec r = ADVec r [DBCol]
    deriving (Show, Read)

-- | Data vectors that reference single nodes in an algebra graph
--  (used for X100 with an n-ary storage model).
type NDVec = ADVec AlgNode

instance DagVector NDVec where
    vectorNodes (ADVec q _) = [q]

    updateVector n1 n2 (ADVec q cols)
        | q == n1   = ADVec n2 cols
        | otherwise = ADVec q cols

--------------------------------------------------------------------------------
-- Abstract vector types for vectorization

-- | A VL data vector references an operator in a VL DAG.
newtype VLDVec = VLDVec AlgNode
    deriving (Show, Read)

instance DagVector VLDVec where
    vectorNodes (VLDVec q) = [q]

    updateVector n1 n2 (VLDVec q)
        | q == n1   = VLDVec n2
        | otherwise = VLDVec q

-- | Replication vectors. A @NRVec@ simply references a node in an
-- algebra Dag.
newtype VLRVec = VLRVec AlgNode

-- | Rekeying vectors. A @NKVec@ simply references a node in an algebra
-- Dag.
newtype VLKVec = VLKVec AlgNode

-- | Filtering vectors. A @NFVec@ simply references a node in an algebra
-- Dag.
newtype VLFVec = VLFVec AlgNode

-- | Sorting vectors. A @NSVec@ simply references a node in an algebra
-- Dag.
newtype VLSVec = VLSVec AlgNode

$(deriveJSON defaultOptions ''ADVec)
$(deriveJSON defaultOptions ''VLRVec)
$(deriveJSON defaultOptions ''VLKVec)
$(deriveJSON defaultOptions ''VLSVec)
$(deriveJSON defaultOptions ''VLFVec)
$(deriveJSON defaultOptions ''VLDVec)
