module Language.ParallelLang.VL.Data.Query where

import Language.ParallelLang.FKL.Render.Render()
import Language.ParallelLang.FKL.Data.FKL
import qualified Language.ParallelLang.Common.Data.Type as T


data Query a =
         TupleVector [Query a]
       | DescrVector a
       | ValueVector a
       | PrimVal a
       | NestedVector a (Query a)
       | PropVector a
       | Closure String [(String, Query a)] (Expr T.Type) (Expr T.Type)
       | AClosure [(String, Query a)] (Expr T.Type) (Expr T.Type)
     deriving Show

nestingDepth :: Query a -> Int
nestingDepth (ValueVector _) = 1
nestingDepth (NestedVector _ r) = 1 + nestingDepth r
nestingDepth _                  = error "Not a list vector"
       
data XML = XML Int String

data SQL = SQL Int Schema String

type Schema = (String, Maybe (String, Int))
    
instance Show SQL where
    show (SQL _ _ s) = s
    
instance Show XML where
    show (XML _ s) = s