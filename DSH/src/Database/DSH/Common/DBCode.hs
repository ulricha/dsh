module Database.DSH.Common.DBCode where

data X100Code = X100Code String
     
newtype SqlCode = SqlCode String

instance Show X100Code where
    show (X100Code s) = s

instance Show SqlCode where
    show (SqlCode s) = s
