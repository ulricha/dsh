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

-- | Is the table guaranteed to be not empty?
data Emptiness = NonEmpty
               | PossiblyEmpty
               deriving (Eq, Ord, Show, Data, Typeable, Generic)

-- | Catalog information hints that users may give to DSH
data TableHints = TableHints 
    { keysHint     :: [Key]
    , nonEmptyHint :: Emptiness
    } deriving (Eq, Ord, Show, Data, Typeable, Generic)

-- | Identifiers
type Ident = String

-----------------------------------------------------------------------------
-- Scalar operators

data UnCastOp = CastDouble
                deriving (Show, Read, Eq, Ord, Generic, Data, Typeable)

data UnBoolOp = Not
                deriving (Show, Read, Eq, Ord, Generic, Data, Typeable)

data UnNumOp = Sin 
             | Cos 
             | Tan 
             | ASin 
             | ACos 
             | ATan 
             | Sqrt 
             | Exp 
             | Log
             deriving (Show, Read, Eq, Ord, Generic, Data, Typeable)

data ScalarUnOp = SUNumOp UnNumOp 
                | SUBoolOp UnBoolOp
                | SUCastOp UnCastOp
                | SUDateOp
                deriving (Show, Read, Eq, Ord, Generic, Data, Typeable)

data BinNumOp = Add 
              | Sub 
              | Div 
              | Mul 
              | Mod
              deriving (Show, Read, Eq, Ord, Generic, Data, Typeable)

data BinRelOp = Eq 
              | Gt 
              | GtE 
              | Lt 
              | LtE
              deriving (Show, Read, Eq, Ord, Generic, Data, Typeable)

data BinBoolOp = Conj 
               | Disj
                deriving (Show, Read, Eq, Ord, Generic, Data, Typeable)

data BinStringOp = Like -- | StringAppend | Contains
                   deriving (Show, Read, Eq, Ord, Generic, Data, Typeable)

-- FIXME this would be a good fit for PatternSynonyms
data ScalarBinOp = SBNumOp BinNumOp
                 | SBRelOp BinRelOp
                 | SBBoolOp BinBoolOp
                 | SBStringOp BinStringOp
                 deriving (Show, Read, Eq, Ord, Generic, Data, Typeable)


-----------------------------------------------------------------------------
-- Join operator arguments: limited expressions that can be used on joins

data JoinConjunct = JoinConjunct JoinExpr BinRelOp JoinExpr

data JoinBinOp = JBNumOp BinNumOp
               | JBStringOp BinStringOp
               deriving (Show, Read, Eq, Ord, Generic, Data, Typeable)

data JoinUnOp = JUNumOp UnNumOp
              | JUCastOp UnCastOp
              deriving (Show, Read, Eq, Ord, Generic, Data, Typeable)

data JoinExpr = JBinOp Type JoinBinOp JoinExpr JoinExpr
              | JUnOp Type JoinUnOp JoinExpr
              | JFst Type JoinExpr
              | JSnd Type JoinExpr
              | JLit Type Val 
              | JInput Type
              deriving (Eq, Ord, Generic, Data, Typeable)

instance Typed JoinExpr where
    typeOf (JBinOp t _ _ _) = t
    typeOf (JUnOp t _ _)    = t
    typeOf (JFst t _)       = t
    typeOf (JSnd t _)       = t
    typeOf (JLit t _)       = t
    typeOf (JInput t)       = t
              
instance Show JoinExpr where
    show (JBinOp _ op e1 e2) = parenthize e1 +++ show op +++ parenthize e2
    show (JUnOp _ op e1)     = show op +++ parenthize e1
    show (JFst _ e)          = "fst" +++ parenthize e
    show (JSnd _ e)          = "snd" +++ parenthize e
    show (JLit _ v)          = show v
    show (JInput _)          = "input"
    
(+++) :: String -> String -> String
s1 +++ s2 = s1 ++ " " ++ s2
    
parenthize :: JoinExpr -> String
parenthize e =
    case e of
        JBinOp _ _ _ _ -> "(" ++ show e ++ ")"
        JUnOp _ _ _    -> "(" ++ show e ++ ")"
        JFst _ _       -> "(" ++ show e ++ ")"
        JSnd _ _       -> "(" ++ show e ++ ")"
        JLit  _ _      -> show e
        JInput _       -> show e
