{-# LANGUAGE DeriveGeneric #-}

module Database.DSH.VL.Data.DBVector
  ( DBCol
  , DVec(..)
  , PVec(..)
  , RVec(..)
  , AlgNode
  , GraphM) where

import           Data.Aeson                   (ToJSON)
import           GHC.Generics                 (Generic)

import           Database.Algebra.Dag.Builder
import           Database.Algebra.Dag.Common

import           Database.Algebra.VL.Data

-- Data vectors
data DVec = DVec AlgNode [DBCol]
    deriving (Show, Generic, Read)

-- Propagation vectors
data PVec = PVec AlgNode
    deriving (Generic)

-- Rename vectors
data RVec = RVec AlgNode
    deriving (Generic)
    
instance ToJSON DVec where
instance ToJSON PVec where
instance ToJSON RVec where
