module Language.ParallelLang.VL.Data.GraphVector where

import Language.ParallelLang.VL.Data.DBVector

import Language.ParallelLang.FKL.Render.Render()
import Language.ParallelLang.FKL.Data.FKL hiding (Pair)

type Graph a = GraphM Plan a

data Layout = InColumn Int
            | Nest DBV Layout
            | Pair Layout Layout
    deriving Show

data Plan =
         ValueVector DBV Layout
       | PrimVal DBP Layout
       | Closure String [(String, Plan)] String Expr Expr
       | AClosure String Plan Int [(String, Plan)] String Expr Expr
     deriving Show

columnsInLayout :: Layout -> Int
columnsInLayout (InColumn _) = 1
columnsInLayout (Nest _ _) = 0
columnsInLayout (Pair p1 p2) = columnsInLayout p1 + columnsInLayout p2

zipLayout :: Layout -> Layout -> Layout
zipLayout l1 l2 = let offSet = columnsInLayout l1
                      l2' = incrementPositions offSet l2
                   in Pair l1 l2'

incrementPositions :: Int -> Layout -> Layout
incrementPositions i (InColumn n)  = (InColumn $ n + i)
incrementPositions _i v@(Nest _ _) = v
incrementPositions i (Pair l1 l2)  = Pair (incrementPositions i l1) (incrementPositions i l2)