module Language.ParallelLang.VL.Data.Query where

import Language.ParallelLang.FKL.Data.FKL
import Language.ParallelLang.VL.Data.VectorTypes as T
import Language.ParallelLang.FKL.Render.Render()

data Query a =
         Tuple [Query a]
       | DescrVector a
       | ValueVector a
       | PrimVal a
       | NestedVector a (Query a)
       | PropVector a
       | UnEvaluated (Expr T.VType)
     deriving Show
       
data XML = XML Int String

data SQL = SQL Int String
    
instance Show SQL where
    show (SQL _ s) = s
    
instance Show XML where
    show (XML _ s) = s
