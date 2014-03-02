{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DeriveDataTypeable #-}
module Database.DSH.Common.Data.Op where

import Data.Data
import Data.Typeable()
import GHC.Generics (Generic) 

data Op = Op ScalarBinOp Bool
    deriving (Eq, Ord, Generic)
    
data ScalarBinOp = Add 
                 | Sub 
                 | Div 
                 | Mul 
                 | Mod 
                 | Eq  
                 | Gt  
                 | GtE 
                 | Lt  
                 | LtE 
                 | Cons 
                 | Conj 
                 | Disj 
                 | Like
    deriving (Eq, Ord, Generic, Data, Typeable)

data ScalarUnOp = Not
                | CastDouble
                | Sin | Cos | Tan
                | ASin | ACos | ATan
                | Sqrt | Exp | Log
                deriving (Eq, Ord, Generic, Data, Typeable)
    
instance Show ScalarBinOp where
    show Add = "+"
    show Sub = "-"
    show Div = "/"
    show Mul = "*"
    show Mod = "%"
    show Eq  = "=="
    show Gt  = ">"
    show GtE = ">="
    show Lt  = "<"
    show LtE = "<="
    show Cons = ":"
    show Conj = "&&"
    show Disj = "||"
    show Like = "LIKE"

instance Show ScalarUnOp where
    show Not        = "not"
    show CastDouble = "double"
    show Sin        = "sin"
    show Cos        = "cos"
    show Tan        = "tan"
    show Log        = "log"
    show Exp        = "exp"
    show Sqrt       = "sqrt"
    show ASin       = "asin"
    show ACos       = "acos"
    show ATan       = "atan"
    
instance Show Op where
    show (Op o True) = show o ++ "^" ++ "1"
    show (Op o False) = show o
