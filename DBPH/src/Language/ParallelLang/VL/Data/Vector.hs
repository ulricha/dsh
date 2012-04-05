module Language.ParallelLang.VL.Data.Vector where

import Database.Algebra.Dag.Common
import qualified Database.Algebra.Dag.Builder as G

import Language.ParallelLang.Common.Data.Type

import Language.ParallelLang.FKL.Render.Render()
import Language.ParallelLang.FKL.Data.FKL


type Graph a = G.GraphM Plan a

type Gam = G.Gam Plan

type Plan = Query AlgNode

data Layout a = Descriptor
              | Content (Position a)
      deriving Show

data Position a = InColumn Int
                | Nest (Query a)
                | Pair (Position a) (Position a)
    deriving Show

data Query a =
--         PairVector (Query a) (Query a)
         ValueVector (Layout a) a
       | PrimVal (Layout a) a
       | Closure String [(String, Query a)] String Expr Expr
       | AClosure String (Query a) Int [(String, Query a)] String Expr Expr
     deriving Show

data PropVector = PropVector AlgNode

data RenameVector = RenameVector AlgNode

{-
nestingDepth :: Show a => Query a -> Int
nestingDepth (ValueVector _) = 1
nestingDepth (NestedVector _ r) = 1 + nestingDepth r
nestingDepth (AClosure _ q _ _ _ _ _) = nestingDepth q 
nestingDepth v                  = error $ "nestingDepth: Not a list vector" ++ show v
-}

data X100 = X100 Int String

data XML = XML Int String

data SQL = SQL Int Schema String

type Schema = (String, Maybe (String, Int))

instance Show X100 where
    show (X100 _ s) = s

instance Show SQL where
    show (SQL _ _ s) = s

instance Show XML where
    show (XML _ s) = s

