{-# LANGUAGE TypeFamilies #-}

-- | This module provides an abstraction over flat relational backends
-- w.r.t. to query execution and result value construction.
module Database.DSH.Backend
    ( TableInfo
    , Backend(..)
    , Row(..)
    ) where

import           Database.DSH.Common.QueryPlan
import qualified Database.DSH.Common.Type        as T
import qualified Database.DSH.Frontend.Internals as F
import qualified Database.DSH.VL.Lang            as VL
import           Database.DSH.VL.Vector

-- FIXME implement properly
type TableInfo = [(String, String, (T.Type -> Bool))]

-- | An abstract backend on which flat queries can be executed.
class Backend c where
    data BackendRow c
    data BackendCode c

    execFlatQuery :: c -> BackendCode c -> IO [BackendRow c]
    querySchema   :: c -> String -> IO TableInfo
    generateCode  :: QueryPlan VL.VL VLDVec -> Shape (BackendCode c)

-- | Abstraction over result rows for a specific backend.
class Row r where
    -- | The type of single attribute values
    data Scalar r

    -- | Look up an attribute in the row
    col       :: String -> r -> (Scalar r)

    -- | Convert an attribute value to a segment descriptor value
    descrVal  :: Scalar r -> Int

    -- | Convert an attribute value to a value term
    scalarVal :: Scalar r -> F.Type a -> F.Exp a
