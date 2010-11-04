-- |
-- This module is intended to be imported @qualified@, to avoid name clashes
-- with "Prelude" functions. For example:
--
-- > import qualified Database.DSH as Q
-- > import Database.DSH (Q)
--
-- Alternatively you can hide "Prelude" and import this module like this:
--
-- > import Prelude ()
-- > import Database.DSH
--
-- In this case you still get Prelude definitions that are not provided
-- by Database.DSH.

module Database.DSH
  (
    module Database.DSH.Combinators

    -- * Data Types
  , Q
  , Time

    -- * Type Classes
  , QA
  , TA, table, tableWithKeys, BasicType
  , View, view, fromView, tuple, record

    -- * Quasiquoter
  , qc

    -- * Template Haskell: Creating Table Representations
  , generateRecords
  , generateInstances

  , module Data.Text
  , module Database.HDBC
  , module Prelude
  )
  where

import Database.DSH.Data (Q, QA, TA, Time, table, tableWithKeys, BasicType, View, view, fromView, tuple, record)
import Database.DSH.QQ (qc)
import Database.DSH.TH (generateRecords, generateInstances)

import Database.DSH.Combinators

import Data.Text (Text)
import Database.HDBC

import Prelude hiding (
    not
  , (&&)
  , (||)
  , (==)
  , (/=)
  , (<)
  , (<=)
  , (>=)
  , (>)
  , head
  , tail
  , take
  , drop
  , map
  , filter
  , last
  , init
  , null
  , length
  , (!!)
  , reverse
  , and
  , or
  , any
  , all
  , sum
  , product
  , concat
  , concatMap
  , maximum
  , minimum
  , replicate
  , splitAt
  , takeWhile
  , dropWhile
  , span
  , break
  , elem
  , notElem
  , zip
  , zipWith
  , unzip
  , fst
  , snd
  )