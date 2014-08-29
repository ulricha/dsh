{-# LANGUAGE TemplateHaskell #-}

-- | A QueryPlan describes the computation of the top-level query
-- result from algebraic plans over some algebra and describes how the
-- result's structure is encoded by the individual queries.
module Database.DSH.Common.QueryPlan where

import           Data.Aeson.TH

import           Database.Algebra.Dag
import           Database.Algebra.Dag.Build
import           Database.Algebra.Dag.Common

import           Database.DSH.VL.Vector

-- | A Layout describes the tuple structure of values encoded by
-- one particular query from a bundle.
data Layout q = InColumn Int
              | Nest q (Layout q)
              | Pair (Layout q) (Layout q)
              deriving (Show, Read)

-- | A Shape describes the structure of the result produced by a
-- bundle of nested queries. 'q' is the type of individual queries,
-- e.g. plan entry nodes or rendered database code.
data Shape q = ValueVector q (Layout q)
             | PrimVal q (Layout q)
             deriving (Show, Read)

$(deriveJSON defaultOptions ''Layout)
$(deriveJSON defaultOptions ''Shape)

-- | Extract all plan root nodes stored in the layout
rootsFromLayout :: DagVector v => Layout v -> [AlgNode]
rootsFromLayout (InColumn _)     = []
rootsFromLayout (Nest v lyt)     = vectorNodes v ++ rootsFromLayout lyt
rootsFromLayout (Pair lyt1 lyt2) = (rootsFromLayout lyt1) ++ (rootsFromLayout lyt2)

-- | Extract all plan root nodes stored in the shape
rootsFromShape :: DagVector v => Shape v -> [AlgNode]
rootsFromShape (ValueVector v lyt) = vectorNodes v ++ rootsFromLayout lyt
rootsFromShape (PrimVal v lyt)     = vectorNodes v ++ rootsFromLayout lyt

-- | Replace a node in a top shape with another node.
updateShape :: DagVector v => AlgNode -> AlgNode -> Shape v -> Shape v
updateShape old new shape =
    case shape of
        ValueVector dbv lyt -> ValueVector (updateVector old new dbv) (updateLayout lyt)
        PrimVal dbv lyt -> PrimVal (updateVector old new dbv) (updateLayout lyt)

  where
    updateLayout (Nest dbv lyt)   = Nest (updateVector old new dbv) (updateLayout lyt)
    updateLayout (Pair lyt1 lyt2) = Pair (updateLayout lyt1) (updateLayout lyt2)
    updateLayout l                = l

columnsInLayout :: Layout q -> Int
columnsInLayout (InColumn _) = 1
columnsInLayout (Nest _ _)   = 0
columnsInLayout (Pair p1 p2) = columnsInLayout p1 + columnsInLayout p2

isOuterMost :: AlgNode -> Shape NDVec -> Bool
isOuterMost n (ValueVector (ADVec n' _) _) = n == n'
isOuterMost n (PrimVal (ADVec n' _) _)     = n == n'

-- | A query plan consists of a DAG over some algebra and information about the
-- shape of the query.
data QueryPlan a v =
  QueryPlan { queryDag   :: AlgebraDag a
            , queryShape :: Shape v
            , queryTags  :: NodeMap [Tag]
            }

-- | Construct a query plan from the operator map and the description
-- of the result shape.
mkQueryPlan :: (Operator a, DagVector v) => AlgMap a -> Shape v -> NodeMap [Tag] -> QueryPlan a v
mkQueryPlan opMap shape tagMap =
  let rs                     = rootsFromShape shape
      d                      = mkDag (reverseAlgMap opMap) rs
  in QueryPlan { queryDag    = d
               , queryShape  = shape
               , queryTags   = tagMap 
               }
