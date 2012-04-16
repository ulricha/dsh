module Language.ParallelLang.VL.Data.Vector where

import Database.Algebra.Dag.Common
import qualified Database.Algebra.Dag.Builder as G

import Language.ParallelLang.FKL.Render.Render()
import Language.ParallelLang.FKL.Data.FKL hiding (Pair)


type Graph a = G.GraphM Plan a

type Gam = G.Gam Plan

type Plan = Query AlgNode

data Layout a = InColumn Int
                | Nest a (Layout a)
                | Pair (Layout a) (Layout a)
    deriving Show

data Query a =
         ValueVector (Layout a) a
       | PrimVal (Layout a) a
       | Closure String [(String, Query a)] String Expr Expr
       | AClosure String (Query a) Int [(String, Query a)] String Expr Expr
     deriving Show

data DescrVector = DescrVector AlgNode

data PropVector = PropVector AlgNode

data RenameVector = RenameVector AlgNode

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

columnsInLayout :: Layout a -> Int
columnsInLayout (InColumn _) = 1
columnsInLayout (Nest _ _) = 0
columnsInLayout (Pair p1 p2) = columnsInLayout p1 + columnsInLayout p2

zipLayout :: Layout a -> Layout a -> Layout a
zipLayout l1 l2 = let offSet = columnsInLayout l1
                      l2' = incrementPositions offSet l2
                   in Pair l1 l2'

incrementPositions :: Int -> Layout a -> Layout a
incrementPositions i (InColumn n)  = (InColumn $ n + i)
incrementPositions _i v@(Nest _ _) = v
incrementPositions i (Pair l1 l2)  = Pair (incrementPositions i l1) (incrementPositions i l2)