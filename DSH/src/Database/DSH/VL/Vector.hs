{-# LANGUAGE DeriveGeneric #-}

-- | This module defines the kinds of vectors that occur in VL
-- programs.
module Database.DSH.VL.Vector
    ( DBCol
    , DVec(..)
    , PVec(..)
    , RVec(..)
    ) where

import           Data.Aeson                   (ToJSON)
import           GHC.Generics                 (Generic)

import           Database.Algebra.Dag.Common

import           Database.DSH.VL.Lang

-- | Data vectors. A data vector references a node in a VL DAG and
-- stores the number of payload columns that it has.
data DVec = DVec AlgNode [DBCol]
    deriving (Show, Generic, Read)

-- | Propagation vectors. A @PVec@ simply references a node in a VL Dag.
data PVec = PVec AlgNode
    deriving (Generic)

-- | Rename vectors. A @RVec@ simply references a node in a VL Dag.
data RVec = RVec AlgNode
    deriving (Generic)
    
instance ToJSON DVec where
instance ToJSON PVec where
instance ToJSON RVec where
