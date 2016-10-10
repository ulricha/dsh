{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeSynonymInstances #-}

-- | This module defines the kinds of vectors that occur in SL and VSL programs.
module Database.DSH.Common.Vector
    ( ColName
    , RelationalVector(..)
    , DagVector
    , vectorNodes
    , updateVector
    , DVec(..)
    , RVec(..)
    , KVec(..)
    , SVec(..)
    , FVec(..)
    ) where

import           Data.Aeson.TH
import qualified Data.Vector                 as V

import           Database.Algebra.Dag.Common

type ColName = String

--------------------------------------------------------------------------------
-- Abstractions over data vectors

-- | Concrete relational encodings of segment vectors have to provide
-- segment-key relations (foreign-key relations) between outer and inner vectors
-- as well as payload columns.
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
-- Abstract vector types for vectorization

-- | An abstract segment data vector
newtype DVec = DVec AlgNode
    deriving (Show, Read)

instance DagVector DVec where
    vectorNodes (DVec q) = [q]

    updateVector n1 n2 (DVec q)
        | q == n1   = DVec n2
        | otherwise = DVec q

-- | Replication vectors.
newtype RVec = RVec AlgNode deriving (Show)

-- | Rekeying vectors.
newtype KVec = KVec AlgNode deriving (Show)

-- | Filtering vectors.
newtype FVec = FVec AlgNode deriving (Show)

-- | Sorting vectors.
newtype SVec = SVec AlgNode deriving (Show)

$(deriveJSON defaultOptions ''RVec)
$(deriveJSON defaultOptions ''KVec)
$(deriveJSON defaultOptions ''SVec)
$(deriveJSON defaultOptions ''FVec)
$(deriveJSON defaultOptions ''DVec)
