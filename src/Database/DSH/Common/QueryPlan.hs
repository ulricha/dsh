{-# LANGUAGE InstanceSigs    #-}
{-# LANGUAGE TemplateHaskell #-}

-- | A QueryPlan describes the computation of the top-level query
-- result from algebraic plans over some algebra and describes how the
-- result's structure is encoded by the individual queries.
module Database.DSH.Common.QueryPlan where

import           Data.Aeson
import           Data.Aeson.TH
import qualified Data.ByteString.Lazy.Char8  as BL
import qualified Data.Foldable               as F
import qualified Data.Traversable            as T
import           Control.Applicative

import           Database.Algebra.Dag
import           Database.Algebra.Dag.Common

import           Database.DSH.Common.Vector

-- | A Layout describes the tuple structure of values encoded by
-- one particular query from a bundle.
data Layout q = LCol
              | LNest q (Layout q)
              | LTuple [Layout q]
              deriving (Show, Read)

instance Functor Layout where
    fmap _ LCol          = LCol
    fmap f (LNest q lyt) = LNest (f q) (fmap f lyt)
    fmap f (LTuple lyts) = LTuple (fmap (fmap f) lyts)

instance F.Foldable Layout where
    foldr _ z LCol          = z
    foldr f z (LNest q lyt) = f q (F.foldr f z lyt)
    foldr f z (LTuple lyts) = F.foldr (\l b -> F.foldr f b l) z lyts

instance T.Traversable Layout where
    traverse _ LCol          = pure LCol
    traverse f (LNest q lyt) = LNest <$> f q <*> T.traverse f lyt
    traverse f (LTuple lyts) = LTuple <$> T.traverse (T.traverse f) lyts

-- | A Shape describes the structure of the result produced by a
-- bundle of nested queries. 'q' is the type of individual vectors,
-- e.g. plan entry nodes or rendered database code. On the top level
-- we distinguish between a single value and a proper vector with more
-- than one element.
data Shape q = VShape q (Layout q)  -- ^ A regular vector shape
             | SShape q (Layout q)  -- ^ A shape for a singleton vector
             deriving (Show, Read)

instance Functor Shape where
    fmap f (VShape q lyt) = VShape (f q) (fmap f lyt)
    fmap f (SShape q lyt) = SShape (f q) (fmap f lyt)

instance F.Foldable Shape where
    foldr f z (VShape q lyt) = f q (F.foldr f z lyt)
    foldr f z (SShape q lyt) = f q (F.foldr f z lyt)

instance T.Traversable Shape where
    traverse f (VShape q lyt) = VShape <$> f q <*> T.traverse f lyt
    traverse f (SShape q lyt) = SShape <$> f q <*> T.traverse f lyt

$(deriveJSON defaultOptions ''Layout)
$(deriveJSON defaultOptions ''Shape)

-- | Extract all plan root nodes stored in the shape
shapeNodes :: DagVector v => Shape v -> [AlgNode]
shapeNodes shape = F.foldMap (\v -> vectorNodes v) shape

-- | Replace a node in a top shape with another node.
updateShape :: DagVector v => AlgNode -> AlgNode -> Shape v -> Shape v
updateShape old new shape = fmap (updateVector old new) shape

-- | Determine the number of relational attributes needed in a vector.
columnsInLayout :: Layout q -> Int
columnsInLayout LCol          = 1
columnsInLayout (LNest _ _)   = 0
columnsInLayout (LTuple lyts) = sum $ map columnsInLayout lyts

-- | A query plan consists of a DAG over some algebra and information about the
-- shape of the query.
data QueryPlan a v = QueryPlan
    { queryDag   :: AlgebraDag a
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

-- | Export a query plan to two files. One file (.plan) contains the
-- DAG for compability with algebra-* dot generators. The other file
-- contains the shape information.
exportPlan :: (ToJSON a, ToJSON v) => String -> QueryPlan a v -> IO ()
exportPlan prefix plan = do
    BL.writeFile (prefix ++ ".plan") (encode $ queryDag plan)
    BL.writeFile (prefix ++ ".shape") (encode $ queryShape plan)
