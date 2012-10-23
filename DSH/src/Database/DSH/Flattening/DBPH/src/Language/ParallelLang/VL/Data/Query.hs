module Language.ParallelLang.VL.Data.Query where
    
data Query a =
         ValueVector a (Layout a)
       | PrimVal a (Layout a)
     deriving Show

data Layout a = InColumn Int
              | Nest a (Layout a)
              | Pair (Layout a) (Layout a)
 deriving Show

data X100 = X100 Int String

data XML = XML Int String

data SQL = SQL Int Schema String

type Schema = (String, [(String, Int)])

instance Show X100 where
    show (X100 _ s) = s

instance Show SQL where
    show (SQL _ _ s) = s

instance Show XML where
    show (XML _ s) = s