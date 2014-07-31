{-# LANGUAGE QuasiQuotes     #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE PatternSynonyms #-}
    
-- | This module performs optimizations on the Nested Kernel Language (NKL).
module Database.DSH.NKL.Opt 
  ( opt ) where
       
import           Debug.Trace

import qualified Data.Set as S

import qualified Database.DSH.NKL.Lang as NKL
import           Database.DSH.NKL.Quote
import           Database.DSH.Impossible

    
