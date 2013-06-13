{-# LANGUAGE GADTs              #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DeriveDataTypeable #-}
module Database.DSH.Flattening.Common.Data.Val where

import Data.Data
import Data.Typeable
import GHC.Generics (Generic)
{-
Basic values in both FKL and NKL. 
-}
data Val where
    ListV   :: [Val] -> Val
    IntV    :: Int -> Val
    BoolV   :: Bool -> Val
    StringV :: String -> Val
    DoubleV :: Double -> Val
    PairV   :: Val -> Val -> Val
    UnitV   :: Val
    deriving (Eq, Show, Ord, Generic, Data, Typeable)
