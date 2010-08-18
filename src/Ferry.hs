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
  , QA , toQ, fromQ
  , TA, table, BasicType
  , View, view,fromView

    -- * Quasiquoter
  , qc, rw

    -- * Template Haskell: Creating Table Representations
  , createTableRepresentation
  , createTableRepresentation'
  )
  where

import Ferry.Combinators
import Ferry.Data (Q)
import Ferry.Class (QA,toQ,fromQ,TA,table,BasicType,View,view,fromView)
import Ferry.QQ2 (qc, rw)
import Ferry.TH (createTableRepresentation, createTableRepresentation')
