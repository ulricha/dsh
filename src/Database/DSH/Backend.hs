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
      -- * Literal scalar value expressions
    , doubleE
    , unitE
    , integerE
    , boolE
    , charE
    , textE
    , decimalE
    , dayE
    ) where

import           Data.Decimal
import           Data.Hashable
import           Data.Text                        (Text)
import           Data.ByteString                  (ByteString)
import qualified Data.Time.Calendar               as C
import           GHC.Generics                     (Generic)

import           Database.DSH.Common.QueryPlan
import           Database.DSH.Common.Vector
import qualified Database.DSH.Frontend.Internals  as F
import           Database.DSH.VL.Lang             (VL)

--------------------------------------------------------------------------------
-- Backend-independent composite keys

data KeyVal = KInt !Int
            | KByteString !ByteString
            | KDay !C.Day
            deriving (Eq, Generic)

newtype CompositeKey = CompositeKey { unCKey :: [KeyVal] }
    deriving (Eq, Generic)

instance Hashable C.Day where
    hashWithSalt s d = s `hashWithSalt` (C.toGregorian d)

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

    boolVal    :: Scalar r -> F.Exp Bool
    integerVal :: Scalar r -> F.Exp Integer
    doubleVal  :: Scalar r -> F.Exp Double
    charVal    :: Scalar r -> F.Exp Char
    textVal    :: Scalar r -> F.Exp Text
    unitVal    :: Scalar r -> F.Exp ()
    decimalVal :: Scalar r -> F.Exp Decimal
    dayVal     :: Scalar r -> F.Exp C.Day

    keyVal :: Scalar r -> KeyVal

--------------------------------------------------------------------------------
-- Constructors for literal scalar type expressions. Backends need
-- those to construct result expressions from rows.

doubleE :: Double -> F.Exp Double
doubleE = F.DoubleE

unitE :: F.Exp ()
unitE = F.UnitE

integerE :: Integer -> F.Exp Integer
integerE = F.IntegerE

boolE :: Bool -> F.Exp Bool
boolE = F.BoolE

charE :: Char -> F.Exp Char
charE = F.CharE

textE :: Text -> F.Exp Text
textE = F.TextE

dayE :: C.Day -> F.Exp C.Day
dayE = F.DayE

decimalE :: Decimal -> F.Exp Decimal
decimalE = F.DecimalE
