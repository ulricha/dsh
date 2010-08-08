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
  , qc

    -- * Template Haskell: Deriving Record Instances
  , deriveRecordInstances
  , createTableRepresentation
  )
  where

import Ferry.Combinators
import Ferry.Data (Q)
import Ferry.Class (QA,toQ,fromQ,TA,table,BasicType,View,view,fromView)
import Ferry.QQ (qc)
import Ferry.TH (deriveRecordInstances, createTableRepresentation)
