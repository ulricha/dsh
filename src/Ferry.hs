-- |
-- This module is intended to be imported @qualified@, to avoid name clashes
-- with "Prelude" functions. For example:
--
-- > import qualified Ferry as Q
-- > import Ferry (Q)

module Ferry
  (
    module Ferry.Combinators

    -- * Data Types
  , Q

    -- * Type Classes
  , QA
  , TA, table, BasicType
  , View, view,fromView

    -- * Quasiquoter
  , qc

    -- * Template Haskell: Creating Table Representations
  , createTableRepresentation
  , createTableRepresentation'
  
  , module Data.Text
  , module Data.Time
  , module Database.HDBC
  , module Prelude
  )
  where

import Ferry.Data (Q,QA,TA,table,BasicType,View,view,fromView)
import Ferry.QQ (qc)
import Ferry.TH (createTableRepresentation, createTableRepresentation')

import Ferry.Combinators

import Data.Text (Text)
import Data.Time (UTCTime)
import Database.HDBC
import Prelude(Eq,Ord,Show,Bool,Char,Integer,Double,IO)


