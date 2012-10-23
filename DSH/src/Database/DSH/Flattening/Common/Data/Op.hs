{-# LANGUAGE DeriveGeneric #-}
module Database.DSH.Flattening.Common.Data.Op where

import GHC.Generics (Generic) 
data Op = Op Oper Bool
    deriving (Eq, Ord, Generic)
    
data Oper = Add 
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
    deriving (Eq, Ord, Generic)
    
instance Show Oper where
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

    
instance Show Op where
    show (Op o True) = show o ++ "^" ++ "1"
    show (Op o False) = show o
