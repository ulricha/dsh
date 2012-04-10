module Language.ParallelLang.VL.Data.Vector where

import Database.Algebra.Dag.Common
import qualified Database.Algebra.Dag.Builder as G

import Language.ParallelLang.Common.Data.Type

import Language.ParallelLang.FKL.Render.Render()
import Language.ParallelLang.FKL.Data.FKL


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

type Schema = (String, Maybe (String, Int))

instance Show X100 where
    show (X100 _ s) = s

instance Show SQL where
    show (SQL _ _ s) = s

instance Show XML where
    show (XML _ s) = s

