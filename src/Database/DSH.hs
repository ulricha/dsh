-- | This module is intended to be imported @qualified@, to avoid name clashes
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
    ( module Database.DSH.Frontend.Externals
    , Q, QA, TA, Elim, elim, View, view, Key(..), TableHints(..), Emptiness(..)
    , module Database.DSH.Frontend.TH
    , module Data.String
    , module Data.Text
    , module Prelude
    ) where

import Database.DSH.Frontend.Externals
import Database.DSH.Frontend.Internals (Q,QA,TA,Elim,elim,View,view,Key(..),TableHints(..), Emptiness(..))
import Database.DSH.Frontend.TH

import Data.String (IsString,fromString)
import Data.Text (Text)
import Prelude hiding (
    not
  , (&&)
  , (||)
  , (==) , (/=)
  , (<)
  , (<=)
  , (>=)
  , (>)
  , (++)
  , mod
  , min
  , max
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
  , (++)
  , reverse
  , and
  , or
  , any
  , all
  , sum
  , concat
  , concatMap
  , maximum
  , minimum
  , splitAt
  , takeWhile
  , dropWhile
  , span
  , break
  , elem
  , notElem
  , lookup
  , zip
  , zipWith
  , unzip
  , zip3
  , zipWith3
  , unzip3
  , fst
  , snd
  , maybe
  , either
  , return
  , (>>=)
  , (>>)
  , div
  )
