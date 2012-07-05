{-# LANGUAGE GADTs, DeriveGeneric #-}
module Language.ParallelLang.Common.Data.Val where

import GHC.Generics (Generic)
{-
Basic values in both FKL and NKL. 
-}
data Val where
    List :: [Val] -> Val
    Int :: Int -> Val
    Bool :: Bool -> Val
    String :: String -> Val
    Double :: Double -> Val
    Pair :: Val -> Val -> Val
    Unit :: Val
    deriving (Eq, Show, Ord, Generic)
