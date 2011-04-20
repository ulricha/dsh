{-# LANGUAGE GADTs, StandaloneDeriving #-}
module Language.ParallelLang.Common.Data.Op where


{-
Constructor for operators.
The string argument represents the operator itself, the int it's nesting depth
-}    
data Op t where
    Op :: String -> Int -> Op (a -> b -> c)
    
deriving instance Eq (Op t)
deriving instance Show (Op t)