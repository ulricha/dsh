{-# LANGUAGE DeriveDataTypeable #-}

module Database.DSH.Common.Data.JoinExpr
    ( JoinExpr(..)
    , UnOp(..)
    ) where
       
import Data.Data
import Data.Typeable
       
import Database.DSH.Common.Data.Op
import Database.DSH.Common.Data.Val

data UnOp = NotJ
          | FstJ
          | SndJ
          deriving (Eq, Ord, Data, Typeable)
          
instance Show UnOp where
    show NotJ = "not"
    show FstJ = "fst"
    show SndJ = "snd"

data JoinExpr = BinOpJ Oper JoinExpr JoinExpr
              | UnOpJ UnOp JoinExpr
              | ConstJ Val
              | InputJ
              deriving (Eq, Ord, Data, Typeable)
              
instance Show JoinExpr where
    show (BinOpJ op e1 e2) = parenthize e1 +++ show op +++ parenthize e2
    show (UnOpJ op e1)     = show op +++ parenthize e1
    show (ConstJ v)        = show v
    show InputJ            = "i"
    
(+++) :: String -> String -> String
s1 +++ s2 = s1 ++ " " ++ s2
    
parenthize :: JoinExpr -> String
parenthize e =
    case e of
        BinOpJ _ _ _ -> "(" ++ show e ++ ")"
        UnOpJ _ _    -> "(" ++ show e ++ ")"
        ConstJ _     -> show e
        InputJ       -> show e
