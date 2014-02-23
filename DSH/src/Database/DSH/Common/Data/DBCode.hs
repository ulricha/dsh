module Database.DSH.Common.Data.DBCode where

data X100Code = X100Code Int String
     
newtype SqlCode = SqlCode String

instance Show X100Code where
    show (X100Code _ s) = s

instance Show SqlCode where
    show (SqlCode s) = s
