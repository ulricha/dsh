{-# LANGUAGE DeriveDataTypeable #-}

module Database.DSH.Flattening.Common.Data.JoinExpr where
       
import Data.Data
import Data.Typeable
       
import Database.DSH.Flattening.Common.Data.Op
import Database.DSH.Flattening.Common.Data.Val

data UnOp = NotJ
          | FstJ
          | SndJ
          deriving (Show, Eq, Ord, Data, Typeable)

data JoinExpr = BinOpJ Oper JoinExpr JoinExpr
              | UnOpJ UnOp JoinExpr
              | ConstJ Val
              | InputJ
              deriving (Show, Eq, Ord, Data, Typeable)
              
