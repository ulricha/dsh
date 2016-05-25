{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- | This module defines the kinds of vectors that occur in SL
-- programs.
module Database.DSH.Common.Vector
    ( DBCol
    , ColName
    , RelationalVector(..)
    , DagVector
    , vectorNodes
    , updateVector
    , ADVec(..)
    , DVec(..)
    , NDVec
    , RVec(..)
    , KVec(..)
    , SVec(..)
    , FVec(..)
    ) where

import           Data.Aeson.TH
import qualified Data.Vector                 as V

import           Database.Algebra.Dag.Common

import           Database.DSH.Common.VectorLang

type ColName = String

--------------------------------------------------------------------------------
-- Abstractions over data vectors

-- | Concrete relational encodings of data vectors explicitly encode ordering
-- and segment information in named columns.
class RelationalVector v where
    rvKeyCols  :: v -> [ColName]
    rvRefCols  :: v -> [ColName]
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

-- | A  data vector references an operator in a  DAG.
newtype DVec = DVec AlgNode
    deriving (Show, Read)

instance DagVector DVec where
    vectorNodes (DVec q) = [q]

    updateVector n1 n2 (DVec q)
        | q == n1   = DVec n2
        | otherwise = DVec q

-- | Replication vectors. A @NRVec@ simply references a node in an
-- algebra Dag.
newtype RVec = RVec AlgNode

-- | Rekeying vectors. A @NKVec@ simply references a node in an algebra
-- Dag.
newtype KVec = KVec AlgNode

-- | Filtering vectors. A @NFVec@ simply references a node in an algebra
-- Dag.
newtype FVec = FVec AlgNode

-- | Sorting vectors. A @NSVec@ simply references a node in an algebra
-- Dag.
newtype SVec = SVec AlgNode

$(deriveJSON defaultOptions ''ADVec)
$(deriveJSON defaultOptions ''RVec)
$(deriveJSON defaultOptions ''KVec)
$(deriveJSON defaultOptions ''SVec)
$(deriveJSON defaultOptions ''FVec)
$(deriveJSON defaultOptions ''DVec)
