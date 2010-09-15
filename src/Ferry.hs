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
  )
  where

import Ferry.Data (Q,QA,TA,table,BasicType,View,view,fromView)
import Ferry.QQ (qc)
import Ferry.TH (createTableRepresentation, createTableRepresentation')

import Ferry.Combinators
