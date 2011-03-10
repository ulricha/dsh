{-# LANGUAGE GADTs #-}
module Language.ParallelLang.Common.Data.Op where


{-
Constructor for operators.
The string argument represents the operator itself, the int it's nesting depth
-}    
data Op where
    Op :: String -> Int -> Op
    deriving (Eq, Show)