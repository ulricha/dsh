{-# LANGUAGE TypeFamilies #-}

-- | This module provides an abstraction over flat relational backends
-- with respect to code generation and query execution.
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

-- | An abstract backend for which we can generate code and on which
-- flat queries can be executed.
class Backend c where
    data BackendRow c
    data BackendCode c
    data BackendPlan c

    -- | Execute a flat query on the backend.
    execFlatQuery :: c -> BackendCode c -> IO [BackendRow c]

    -- | Query the backend for schema information.
    querySchema   :: c -> String -> IO TableInfo

    -- | Implement vector operations using the backend-specific
    -- algebra.
    generatePlan  :: QueryPlan VL.VL VLDVec -> BackendPlan c

    -- | Optimize the algebra plan and generate serialized backend
    -- code
    generateCode  :: BackendPlan c -> Shape (BackendCode c)

    -- | Dump versions of the plan in JSON form to the specified file.
    dumpPlan :: String -> BackendPlan c -> IO ()

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
