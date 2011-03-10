{-# LANGUAGE GADTs #-}
module Language.ParallelLang.Common.Data.Val where

{-
Basic values in both FKL and NKL. 
-}
data Val where
    Int :: Int -> Val
    Bool :: Bool -> Val
    deriving (Eq, Show)
