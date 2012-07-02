module Language.ParallelLang.VL.Data.DBVector(DBCol, DBV(..), DBP(..), DescrVector(..), PropVector(..), RenameVector(..), AlgNode, GraphM, PVal(..)) where

import Database.Algebra.Dag.Common
import Database.Algebra.Dag.Builder

type DBCol = Int

data DBV = DBV AlgNode [DBCol]
    deriving Show

data DBP = DBP AlgNode [DBCol] 
    deriving Show
    
data DescrVector = DescrVector AlgNode

data PropVector = PropVector AlgNode

data RenameVector = RenameVector AlgNode

data PVal = PInt Int
          | PNat Int
          | PBool Bool
          | PString String
          | PDouble Double
          | PUnit
    deriving (Eq, Ord)
