{-# LANGUAGE DeriveDataTypeable #-}

module Database.DSH.Common.Data.JoinExpr
    ( JoinExpr(..)
    , UnOp(..)
    ) where
       
import Data.Data
import Data.Typeable
       
import Database.DSH.Common.Data.Op
import Database.DSH.Common.Data.Val
import Database.DSH.Common.Data.Type

data UnOp = NotJ
          | FstJ
          | SndJ
          deriving (Eq, Ord, Data, Typeable)
          
instance Show UnOp where
    show NotJ = "not"
    show FstJ = "fst"
    show SndJ = "snd"

data JoinExpr = BinOpJ Type Oper JoinExpr JoinExpr
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

