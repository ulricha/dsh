{-# LANGUAGE DeriveGeneric    #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies     #-}

-- | This module provides an abstraction over flat relational backends
-- with respect to code generation and query execution.
module Database.DSH.Backend
    ( -- * Backend-indepdent composite keys
      KeyVal(..)
    , CompositeKey(..)
      -- * Backend Functionality Classes
    , Backend(..)
    , Row(..)
    ) where

import           Data.ByteString                 (ByteString)
import           Data.Hashable
import           Data.Scientific
import           Data.Text                       (Text)
import qualified Data.Time.Calendar              as C
import           GHC.Generics                    (Generic)

import           Database.DSH.Common.QueryPlan
import           Database.DSH.Common.Vector
import           Database.DSH.VL.Lang            (VL)

--------------------------------------------------------------------------------
-- Backend-independent composite keys

data KeyVal = KInt        {-# UNPACK #-} !Int
            | KByteString {-# UNPACK #-} !ByteString
            | KDay                       !C.Day
            deriving (Eq, Generic)

newtype CompositeKey = CompositeKey { unCKey :: [KeyVal] }
    deriving (Eq, Generic)

instance Hashable C.Day where
    hashWithSalt s d = s `hashWithSalt` C.toGregorian d

instance Hashable KeyVal where

instance Hashable CompositeKey where

--------------------------------------------------------------------------------

-- | An abstract backend for which we can generate code and on which
-- flat queries can be executed.
class (RelationalVector (BackendCode c), Row (BackendRow c)) => Backend c where
    data BackendRow c
    data BackendCode c
    data BackendPlan c

    -- | Execute a flat query on the backend.
    execFlatQuery :: c -> BackendCode c -> IO [BackendRow c]

    -- | Implement vector operations using the backend-specific
    -- algebra.
    generatePlan  :: QueryPlan VL VLDVec -> BackendPlan c

    -- | Optimize the algebra plan and generate serialized backend
    -- code
    generateCode  :: BackendPlan c -> Shape (BackendCode c)

    -- | Dump versions of the plan in JSON form to the specified file.
    dumpPlan :: String -> Bool -> BackendPlan c -> IO FilePath

    transactionally :: c -> (c -> IO a) -> IO a

--------------------------------------------------------------------------------

-- | Abstraction over result rows for a specific backend.
class Row r where
    -- | The type of single attribute values
    data Scalar r

    -- | Look up an attribute in the row
    col        :: String -> r -> (Scalar r)

    -- | Convert an attribute value to a segment descriptor value
    descrVal   :: Scalar r -> Int

    boolVal    :: Scalar r -> Bool
    integerVal :: Scalar r -> Integer
    doubleVal  :: Scalar r -> Double
    charVal    :: Scalar r -> Char
    textVal    :: Scalar r -> Text
    decimalVal :: Scalar r -> Scientific
    dayVal     :: Scalar r -> C.Day

    keyVal :: Scalar r -> KeyVal
