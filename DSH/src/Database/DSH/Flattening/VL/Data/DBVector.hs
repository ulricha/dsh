{-# LANGUAGE DeriveGeneric #-}

module Database.DSH.Flattening.VL.Data.DBVector(DBCol, DBV(..), DBP(..), DescrVector(..), PropVector(..), RenameVector(..), AlgNode, GraphM) where

import           Data.Aeson                   (ToJSON)
import           GHC.Generics                 (Generic)

import           Database.Algebra.Dag.Builder
import           Database.Algebra.Dag.Common

type DBCol = Int

data DBV = DBV AlgNode [DBCol]
    deriving (Show, Generic, Read)

data DBP = DBP AlgNode [DBCol]
    deriving (Show, Generic, Read)

data DescrVector = DescrVector AlgNode
    deriving (Generic)

data PropVector = PropVector AlgNode
    deriving (Generic)

data RenameVector = RenameVector AlgNode
    deriving (Generic)
    
instance ToJSON DBV where
instance ToJSON DBP where
instance ToJSON DescrVector where
instance ToJSON PropVector where
instance ToJSON RenameVector where

