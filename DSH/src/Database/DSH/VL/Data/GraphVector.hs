{-# LANGUAGE DeriveGeneric #-}
module Database.DSH.VL.Data.GraphVector where

import Database.DSH.VL.Data.DBVector

import Database.DSH.FKL.Render.Render()
import Database.DSH.FKL.Data.FKL

import GHC.Generics (Generic)

type Graph a = GraphM Shape a

data Layout = InColumn Int
            | Nest DVec Layout
            | Pair Layout Layout
    deriving (Show, Generic)

data Shape = ValueVector DVec Layout
           | PrimVal DVec Layout
           | Closure String [(String, Shape)] String Expr Expr
           | AClosure String Shape Int [(String, Shape)] String Expr Expr
           deriving (Show, Generic)

rootNodes :: Shape -> [AlgNode]
rootNodes (ValueVector (DVec n _) lyt) = n : rootNodes' lyt
rootNodes (PrimVal (DVec n _) lyt)     = n : rootNodes' lyt
rootNodes (Closure _ _ _ _ _)          = error "Function cannot appear as a result value"
rootNodes (AClosure _ _ _ _ _ _ _)     = error "Function cannot appear as a result value"

rootNodes' :: Layout -> [AlgNode]
rootNodes' (Pair p1 p2) = rootNodes' p1 ++ rootNodes' p2
rootNodes' (InColumn _) = []
rootNodes' (Nest (DVec q _) lyt) = q : rootNodes' lyt

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
