module Language.ParallelLang.VL.Data.DBVector(DBCol, DBV(..), DBP(..), AlgNode) where

import Database.Algebra.Dag.Common

type DBCol = Int

data DBV = DBV AlgNode [DBCol]

data DBP = DBP AlgNode [DBCol] 


