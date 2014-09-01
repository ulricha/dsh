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
data Layout q = LCol Int
              | LNest q (Layout q)
              | LPair (Layout q) (Layout q)
              deriving (Show, Read)

-- | A Shape describes the structure of the result produced by a
-- bundle of nested queries. 'q' is the type of individual vectors,
-- e.g. plan entry nodes or rendered database code. On the top level
-- we distinguish between a single value and a proper vector with more
-- than one element.
data Shape q = VShape q (Layout q)  -- | A regular vector shape
             | SShape q (Layout q)  -- | A shape for a singleton vector
             deriving (Show, Read)

$(deriveJSON defaultOptions ''Layout)
$(deriveJSON defaultOptions ''Shape)

-- | Extract all plan root nodes stored in the layout
rootsFromLayout :: DagVector v => Layout v -> [AlgNode]
rootsFromLayout (LCol _)          = []
rootsFromLayout (LNest v lyt)     = vectorNodes v ++ rootsFromLayout lyt
rootsFromLayout (LPair lyt1 lyt2) = (rootsFromLayout lyt1) ++ (rootsFromLayout lyt2)

-- | Extract all plan root nodes stored in the shape
rootsFromShape :: DagVector v => Shape v -> [AlgNode]
rootsFromShape (VShape v lyt) = vectorNodes v ++ rootsFromLayout lyt
rootsFromShape (SShape v lyt) = vectorNodes v ++ rootsFromLayout lyt

-- | Replace a node in a top shape with another node.
updateShape :: DagVector v => AlgNode -> AlgNode -> Shape v -> Shape v
updateShape old new shape =
    case shape of
        VShape dbv lyt -> VShape (updateVector old new dbv) (updateLayout lyt)
        SShape dbv lyt -> SShape (updateVector old new dbv) (updateLayout lyt)

  where
    updateLayout (LNest dbv lyt)   = LNest (updateVector old new dbv) (updateLayout lyt)
    updateLayout (LPair lyt1 lyt2) = LPair (updateLayout lyt1) (updateLayout lyt2)
    updateLayout l                 = l

columnsInLayout :: Layout q -> Int
columnsInLayout (LCol _)      = 1
columnsInLayout (LNest _ _)   = 0
columnsInLayout (LPair p1 p2) = columnsInLayout p1 + columnsInLayout p2

isOuterMost :: AlgNode -> Shape NDVec -> Bool
isOuterMost n (VShape (ADVec n' _) _) = n == n'
isOuterMost n (SShape (ADVec n' _) _) = n == n'

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
