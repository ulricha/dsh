{-# LANGUAGE TemplateHaskell            #-}
module Database.DSH.Translate.NKL2FKL (flatten) where

import           Control.Applicative
import           Control.Monad
import           Control.Monad.State hiding (lift)
import           Data.List
       
import           Database.DSH.Impossible
import qualified Database.DSH.FKL.Lang as F
import qualified Database.DSH.NKL.Lang as N
import qualified Database.DSH.NKL.Rewrite as NR
import           Database.DSH.FKL.Primitives
import           Database.DSH.Common.Type
import           Database.DSH.Common.Lang

flatten = $unimplemented
