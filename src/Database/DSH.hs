-- |
-- This module is intended to be imported @qualified@, to avoid name clashes
-- with "Prelude" functions. For example:
--
-- > import qualified Database.DSH as Q
-- > import Database.DSH (Q)
--
-- Alternatively you can hide "Prelude" and import this module like this:
-- > import Prelude ()
-- > import Database.DSH

module Database.DSH
  (
    module Database.DSH.Combinators

    -- * Data Types
  , Q
  , Time

    -- * Type Classes
  , QA
  , TA, table, tableWithKeys, BasicType
  , View, view,fromView

    -- * Quasiquoter
  , qc

    -- * Template Haskell: Creating Table Representations
  , createTableRepresentation
  , createTableRepresentation'
  
  , module Data.Text
  , module Database.HDBC
  , module Prelude
  )
  where

import Database.DSH.Data (Q,QA,TA,Time,table,tableWithKeys,BasicType,View,view,fromView)
import Database.DSH.QQ (qc)
import Database.DSH.TH (createTableRepresentation, createTableRepresentation')

import Database.DSH.Combinators

import Data.Text (Text)
import Database.HDBC
import Prelude(Eq,Ord,Show,Bool,Char,Integer,Double,IO)


