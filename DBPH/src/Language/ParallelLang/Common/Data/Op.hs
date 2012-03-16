module Language.ParallelLang.Common.Data.Op where

data Op = Op Oper Bool
    deriving (Eq, Ord)
    
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
    deriving (Eq, Ord)
    
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
