{-# LANGUAGE DeriveGeneric #-}

-- | A QueryPlan describes the computation of the top-level query
-- result from algebraic plans over some algebra and describes how the
-- result's structure is encoded by the individual queries.
module Database.DSH.Common.QueryPlan where

import           GHC.Generics                  (Generic)

import           Data.Aeson                    (ToJSON)

import           Database.Algebra.Dag
import           Database.Algebra.Dag.Build
import           Database.Algebra.Dag.Common

import           Database.DSH.VL.Vector
import qualified Database.DSH.VL.Shape         as S

-- | A TopLayout describes the tuple structure of values encoded by
-- one particular query from a bundle.
data TopLayout q = InColumn Int
                 | Nest q (TopLayout q)
                 | Pair (TopLayout q) (TopLayout q)
                 deriving (Show, Read, Generic)

-- | A TopShape describes the structure of the result produced by a
-- bundle of nested queries. 'q' is the type of individual queries,
-- e.g. plan entry nodes or rendered database code.
data TopShape q = ValueVector q (TopLayout q)
                | PrimVal q (TopLayout q)
                deriving (Show, Read, Generic)

instance ToJSON a => ToJSON (TopLayout a) where
instance ToJSON a => ToJSON (TopShape a) where

-- | Extract all plan root nodes stored in the layout
rootsFromTopLayout :: DagVector v => TopLayout v -> [AlgNode]
rootsFromTopLayout (InColumn _)     = []
rootsFromTopLayout (Nest v lyt)     = vectorNodes v ++ rootsFromTopLayout lyt
rootsFromTopLayout (Pair lyt1 lyt2) = (rootsFromTopLayout lyt1) ++ (rootsFromTopLayout lyt2)

-- | Extract all plan root nodes stored in the shape
rootsFromTopShape :: DagVector v => TopShape v -> [AlgNode]
rootsFromTopShape (ValueVector v lyt) = vectorNodes v ++ rootsFromTopLayout lyt
rootsFromTopShape (PrimVal v lyt)     = vectorNodes v ++ rootsFromTopLayout lyt

-- | Replace a node in a top shape with another node.
updateTopShape :: DagVector v => AlgNode -> AlgNode -> TopShape v -> TopShape v
updateTopShape old new shape =
    case shape of
        ValueVector dbv lyt -> ValueVector (updateVector old new dbv) (updateLayout lyt)
        PrimVal dbv lyt -> PrimVal (updateVector old new dbv) (updateLayout lyt)

  where
    updateLayout (Nest dbv lyt)   = Nest (updateVector old new dbv) (updateLayout lyt)
    updateLayout (Pair lyt1 lyt2) = Pair (updateLayout lyt1) (updateLayout lyt2)
    updateLayout l                = l

columnsInLayout :: TopLayout q -> Int
columnsInLayout (InColumn _) = 1
columnsInLayout (Nest _ _)   = 0
columnsInLayout (Pair p1 p2) = columnsInLayout p1 + columnsInLayout p2

isOuterMost :: AlgNode -> TopShape NDVec -> Bool
isOuterMost n (ValueVector (ADVec n' _) _) = n == n'
isOuterMost n (PrimVal (ADVec n' _) _)     = n == n'

-- | Intermediate shapes may contain constructs that are not allowed
-- in top-level queries (e.g. closures). Convert to a safe shape which
-- represents legal top-level results.
exportShape :: S.Shape -> TopShape VLDVec
exportShape (S.ValueVector q lyt) = ValueVector q (exportLayout lyt)
exportShape (S.PrimVal q lyt)     = PrimVal q (exportLayout lyt)
exportShape s                     = error $ "exportShape: impossible top-level shape " ++ (show s)

exportLayout :: S.Layout -> TopLayout VLDVec
exportLayout (S.InColumn i)     = InColumn i
exportLayout (S.Nest q lyt)     = Nest q (exportLayout lyt)
exportLayout (S.Pair lyt1 lyt2) = Pair (exportLayout lyt1) (exportLayout lyt2)

-- | A query plan consists of a DAG over some algebra and information about the
-- shape of the query.
data QueryPlan a v =
  QueryPlan { queryDag   :: AlgebraDag a
            , queryShape :: TopShape v
            , queryTags  :: NodeMap [Tag]
            }

-- | Construct a query plan from the operator map and the description
-- of the result shape.
mkQueryPlan :: (Operator a, DagVector v) => AlgMap a -> TopShape v -> NodeMap [Tag] -> QueryPlan a v
mkQueryPlan opMap shape tagMap =
  let rs                     = rootsFromTopShape shape
      d                      = mkDag (reverseAlgMap opMap) rs
  in QueryPlan { queryDag   = d
               , queryShape = shape
               , queryTags  = tagMap 
               }
