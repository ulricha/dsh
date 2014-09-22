{-# LANGUAGE TemplateHaskell #-}

-- | A QueryPlan describes the computation of the top-level query
-- result from algebraic plans over some algebra and describes how the
-- result's structure is encoded by the individual queries.
module Database.DSH.Common.QueryPlan where

import           Data.Aeson.TH

import           Database.Algebra.Dag
import           Database.Algebra.Dag.Common

import           Database.DSH.VL.Vector

-- | A Layout describes the tuple structure of values encoded by
-- one particular query from a bundle.
data Layout q = LCol Int
              | LNest q (Layout q)
              | LTuple [Layout q]
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
layoutNodes :: DagVector v => Layout v -> [AlgNode]
layoutNodes (LCol _)      = []
layoutNodes (LNest v lyt) = vectorNodes v ++ layoutNodes lyt
layoutNodes (LTuple lyts) = concatMap layoutNodes lyts

-- | Extract all plan root nodes stored in the shape
shapeNodes :: DagVector v => Shape v -> [AlgNode]
shapeNodes (VShape v lyt) = vectorNodes v ++ layoutNodes lyt
shapeNodes (SShape v lyt) = vectorNodes v ++ layoutNodes lyt

-- | Replace a node in a top shape with another node.
updateShape :: DagVector v => AlgNode -> AlgNode -> Shape v -> Shape v
updateShape old new shape =
    case shape of
        VShape dbv lyt -> VShape (updateVector old new dbv) (updateLayout lyt)
        SShape dbv lyt -> SShape (updateVector old new dbv) (updateLayout lyt)

  where
    updateLayout (LNest dbv lyt) = LNest (updateVector old new dbv) (updateLayout lyt)
    updateLayout (LTuple lyts)   = LTuple (map updateLayout lyts)
    updateLayout l               = l

columnsInLayout :: Layout q -> Int
columnsInLayout (LCol _)      = 1
columnsInLayout (LNest _ _)   = 0
columnsInLayout (LTuple lyts) = sum $ map columnsInLayout lyts

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
mkQueryPlan :: (Operator a, DagVector v) 
            => AlgebraDag a 
            -> Shape v 
            -> NodeMap [Tag] 
            -> QueryPlan a v
mkQueryPlan dag shape tagMap =
  QueryPlan { queryDag   = addRootNodes dag (shapeNodes shape)
            , queryShape = shape
            , queryTags  = tagMap 
            }
