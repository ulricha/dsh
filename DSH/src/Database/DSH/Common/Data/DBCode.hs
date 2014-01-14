module Database.DSH.Common.Data.DBCode where

data X100Code = X100Code Int String
     
data SQLCode = SQLCode Int Schema String

type Schema = (String, [(String, Int)])

instance Show X100Code where
    show (X100Code _ s) = s

instance Show SQLCode where
    show (SQLCode _ _ s) = s
