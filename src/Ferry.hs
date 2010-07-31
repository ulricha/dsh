-- |
-- This module is intended to be imported @qualified@, to avoid name clashes
-- with "Prelude" functions. For example:
--
-- > import qualified Ferry as Q
-- > import Ferry (Q)

module Ferry
  (
    module Ferry.Combinators
  , module Ferry.Tuples

    -- * Type Classes
  , Q
  , QA , toQ, fromQ
  , View, view
  , qc

    -- * Template Haskell: Deriving Record Instances
  , deriveRecordInstances
  , createTableRepresentation
  )
  where

import Ferry.Combinators
import Ferry.Tuples
import Ferry.Data (Q)
import Ferry.Class (QA,toQ,fromQ,View,view)
import Ferry.QQ (qc)
import Ferry.TH (deriveRecordInstances, createTableRepresentation)
