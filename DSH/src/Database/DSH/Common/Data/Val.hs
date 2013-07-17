{-# LANGUAGE GADTs              #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DeriveDataTypeable #-}

module Database.DSH.Common.Data.Val where

import Data.Data
import Data.Typeable
import GHC.Generics (Generic)
import Data.List

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
    deriving (Eq, Ord, Generic, Data, Typeable)
    
instance Show Val where
  show (ListV vs)    = "[" ++ (intercalate ", " $ map show vs) ++ "]"
  show (IntV i)      = show i
  show (BoolV b)     = show b
  show (StringV s)   = "\"" ++ show s ++ "\""
  show (DoubleV d)   = show d
  show (PairV v1 v2) = "(" ++ show v1 ++ ", " ++ show v2 ++ ")"
  show UnitV         = "()"
  
