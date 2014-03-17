{-# LANGUAGE GADTs              #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric      #-}

module Database.DSH.Common.Lang where

import Data.Data
import Data.Typeable()
import GHC.Generics

import Data.List

import Database.DSH.Common.Type

-----------------------------------------------------------------------------
-- Join operator arguments: limited expressions that can be used on joins

data UnOp = NotJ
          | FstJ
          | SndJ
          deriving (Eq, Ord, Data, Typeable)
          
instance Show UnOp where
    show NotJ = "not"
    show FstJ = "fst"
    show SndJ = "snd"

data JoinExpr = BinOpJ Type ScalarBinOp JoinExpr JoinExpr
              | UnOpJ Type UnOp JoinExpr
              | ConstJ Type Val
              | InputJ Type
              deriving (Eq, Ord, Data, Typeable)

instance Typed JoinExpr where
    typeOf (BinOpJ t _ _ _) = t
    typeOf (UnOpJ t _ _)    = t
    typeOf (ConstJ t _)     = t
    typeOf (InputJ t)       = t
              
instance Show JoinExpr where
    show (BinOpJ _ op e1 e2) = parenthize e1 +++ show op +++ parenthize e2
    show (UnOpJ _ op e1)     = show op +++ parenthize e1
    show (ConstJ _ v)        = show v
    show (InputJ _)          = "i"
    
(+++) :: String -> String -> String
s1 +++ s2 = s1 ++ " " ++ s2
    
parenthize :: JoinExpr -> String
parenthize e =
    case e of
        BinOpJ _ _ _ _ -> "(" ++ show e ++ ")"
        UnOpJ _ _ _    -> "(" ++ show e ++ ")"
        ConstJ _ _     -> show e
        InputJ _       -> show e

-----------------------------------------------------------------------------
-- Common types for backend expressions

-- | Basic values in both FKL and NKL. 
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

newtype ColName = ColName String deriving (Eq, Ord, Show, Data, Typeable, Generic)
  
-- | Typed table columns
type Column = (ColName, Type)
     
-- | Table keys
newtype Key = Key [ColName] deriving (Eq, Ord, Show, Data, Typeable, Generic)

-- | Identifiers
type Ident = String

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
                 | Conj 
                 | Disj 
                 | Like
    deriving (Read, Eq, Ord, Generic, Data, Typeable)

data ScalarUnOp = Not
                | CastDouble
                | Sin | Cos | Tan
                | ASin | ACos | ATan
                | Sqrt | Exp | Log
                deriving (Read, Eq, Ord, Generic, Data, Typeable)
    
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
