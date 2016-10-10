{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}

module Database.DSH.VSL.VirtualSegmentAlgebra where

import qualified Data.List.NonEmpty                as N
import           Database.Algebra.Dag.Build
import qualified Database.DSH.Common.Lang          as L
import           Database.DSH.Common.VectorLang
import           Database.DSH.VSL.Lang

-- | This class defines the dialect of segment operators that implement delayed
-- vectors. These operators that need to be implemented by a backend.
class VirtualSegmentAlgebra a where
    -- | Data Vector
    type VSLDVec a

    -- | Replication Vector
    type VSLRVec a

    -- | Turn a flat vector into a nested vector with one segment.
    vecNest :: VSLDVec a -> Build a (VSLDVec a, VSLDVec a)

    -- | A vector representing a literal list.
    vecLit :: PType -> VecSegs -> Build a (VSLDVec a)

    -- | A reference to a database-resident table.
    vecTableRef :: String -> L.BaseTableSchema -> Build a (VSLDVec a)

    -- | Perform duplicate elimination per segment.
    vecDistinct :: VSLDVec a -> Build a (VSLDVec a)

    -- | /Materialize/ vector positions per segment. The operator adds
    -- an item column that contains the dense positions of the
    -- vector's elements in each segment.
    vecNumber :: VSLDVec a -> Build a (VSLDVec a)

    -- | Produce a *merge map* from a vector @v@ that maps all segments of the
    -- key domain of @v@ to the corresponding segment of @v@ (i.e. merge
    -- segments of inner vectors).
    vecMergeMap :: VSLDVec a -> Build a (VSLRVec a)

    -- | From a vector @v@ produce a segment map that maps every segment induced
    -- by the key domain of @v@ to the unit segment.
    vecUnitMap :: VSLDVec a -> Build a (VSLRVec a)

    -- | Update the segment map such that every segment points to the unit
    -- segment.
    vecUpdateUnit :: VSLRVec a -> Build a (VSLRVec a)

    -- | From a vector with only one segment, create a segmented
    -- version in which every value in the original segment inhabits
    -- its own segment.
    vecSegment :: VSLDVec a -> Build a (VSLDVec a)

    -- | Turn a vector with multiple vectors into a vector with only the unit
    -- segment.
    vecUnsegment :: VSLDVec a -> Build a (VSLDVec a)

    vecAggr :: N.NonEmpty AggrFun -> VSLDVec a -> Build a (VSLDVec a)
    vecFold :: AggrFun -> VSLDVec a -> Build a (VSLDVec a)

    vecWinFun :: WinFun -> FrameSpec -> VSLDVec a -> Build a (VSLDVec a)

    -- | Reverse each segment of a vector individually.
    vecReverse :: VSLDVec a -> Build a (VSLDVec a, VSLRVec a)

    -- | Filter a vector by applying a scalar boolean predicate.
    vecSelect:: VectorExpr -> VSLDVec a -> Build a (VSLDVec a, VSLRVec a)

    -- | Per-segment sorting of a vector.
    vecSort :: VectorExpr -> VSLDVec a -> Build a (VSLDVec a, VSLRVec a)

    -- | Per-segment grouping of a vector
    vecGroup :: VectorExpr -> VSLDVec a -> Build a (VSLDVec a, VSLDVec a, VSLRVec a)

    -- | The VL aggregation operator groups every segment of the input vector by the
    -- given columns and then performs the list of aggregations described by the
    -- second argument. The result vector has the same segment structure as the
    -- input vector since all segments are grouped individually. The output
    -- payload columns are the grouping columns followed by the aggregation
    -- results.
    vecGroupAggr :: VectorExpr -> AggrFun -> VSLDVec a -> Build a (VSLDVec a)

    -- | Construct a new vector as the result of a list of scalar
    -- expressions per result column.
    vecProject :: VectorExpr -> VSLDVec a -> Build a (VSLDVec a)

    -- | Combine a replication vector and a vector containing physical segments.
    vecMaterialize :: VSLRVec a -> VSLDVec a -> Build a (VSLDVec a, VSLRVec a)

    -- | Replicate each entry of the left input vector over the corresponding
    -- segment in the right input vector.
    vecReplicateSeg :: VSLDVec a -> VSLDVec a -> Build a (VSLDVec a, VSLRVec a)

    -- | Replicate the single scalar value in the left input vector to all elements
    -- of the right input vector.
    vecReplicateScalar :: VSLDVec a -> VSLDVec a -> Build a (VSLDVec a, VSLRVec a)

    -- | Unbox singleton segments from an inner vector.
    vecUnboxSng :: VSLDVec a -> VSLDVec a -> Build a (VSLDVec a, VSLRVec a)

    -- | Unbox singleton segments from an inner vector. Insert default values
    -- for missing segments.
    vecUnboxDefault :: N.NonEmpty L.ScalarVal -> VSLDVec a -> VSLDVec a -> Build a (VSLDVec a, VSLRVec a)

    -- | Update the right input segment map by composing with the left input
    -- map.
    vecUpdateMap :: VSLRVec a -> VSLRVec a -> Build a (VSLRVec a)

    -- | Per-segment append of two vectors.
    vecAppend :: VSLDVec a -> VSLDVec a -> Build a (VSLDVec a, VSLRVec a, VSLRVec a)

    -- | Align two vectors positionally. However, in contrast to 'vecZip', these
    -- are not arbitrary vectors, but vectors which are guaranteed to have the
    -- same length because they are operands to lifted operators.
    vecAlign :: VSLDVec a -> VSLDVec a -> Build a (VSLDVec a)

    -- | Positionally align two vectors per segment: @map zip xss yss@.
    vecZip :: VSLDVec a -> VSLDVec a -> Build a (VSLDVec a, VSLRVec a, VSLRVec a)

    vecCartProduct :: VSLDVec a -> VSLDVec a -> Build a (VSLDVec a, VSLRVec a, VSLRVec a)
    vecThetaJoin :: SegmentLookup -> SegmentLookup -> L.JoinPredicate VectorExpr -> VSLDVec a -> VSLDVec a -> Build a (VSLDVec a, VSLRVec a, VSLRVec a)
    vecNestJoin :: SegmentLookup -> SegmentLookup -> L.JoinPredicate VectorExpr -> VSLDVec a -> VSLDVec a -> Build a (VSLDVec a, VSLRVec a, VSLRVec a)
    vecSemiJoin :: SegmentLookup -> SegmentLookup -> L.JoinPredicate VectorExpr -> VSLDVec a -> VSLDVec a -> Build a (VSLDVec a, VSLRVec a)
    vecAntiJoin :: SegmentLookup -> SegmentLookup -> L.JoinPredicate VectorExpr -> VSLDVec a -> VSLDVec a -> Build a (VSLDVec a, VSLRVec a)
    vecGroupJoin :: SegmentLookup -> SegmentLookup -> L.JoinPredicate VectorExpr -> L.NE AggrFun -> VSLDVec a -> VSLDVec a -> Build a (VSLDVec a)

    vecCombine :: VSLDVec a -> VSLDVec a -> VSLDVec a -> Build a (VSLDVec a, VSLRVec a, VSLRVec a)
