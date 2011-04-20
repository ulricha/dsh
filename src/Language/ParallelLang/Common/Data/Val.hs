{-# LANGUAGE GADTs, StandaloneDeriving  #-}
module Language.ParallelLang.Common.Data.Val where

{-
Basic values in both FKL and NKL. 
-}
data Val t where
    Int :: Int -> Val Int
    Bool :: Bool -> Val Bool
    String :: String -> Val String
    Double :: Double -> Val Double
    Unit :: Val ()

deriving instance Eq (Val t)
deriving instance Show (Val t)