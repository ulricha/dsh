{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}

module Database.DSH.SL.SegmentAlgebra where

import qualified Data.List.NonEmpty                as N
import           Database.Algebra.Dag.Build
import qualified Database.DSH.Common.Lang          as L
import           Database.DSH.Common.Type
import           Database.DSH.Common.VectorLang

-- | This class defines the segment operators that need to be implemented by a
-- backend.
class SegmentAlgebra a where
    -- | Data Vector
    type DVec a

    -- | Re-Keying Vector
    type KVec a

    -- | Replication Vector
    type RVec a

    -- | Sorting Vector
    type SVec a

    -- | Filtering Vector
    type FVec a

    -- | Turn a flat vector into a nested vector with one segment.
    vecNest :: DVec a -> Build a (DVec a, DVec a)

    -- | A vector representing a literal list.
    vecLit :: [ScalarType] -> SegFrame -> Segments -> Build a (DVec a)

    -- | A reference to a database-resident table.
    vecTableRef :: String -> L.BaseTableSchema -> Build a (DVec a)

    -- | Perform duplicate elimination per segment.
    vecUnique :: DVec a -> Build a (DVec a)

    -- | /Materialize/ vector positions per segment. The operator adds
    -- an item column that contains the dense positions of the
    -- vector's elements in each segment.
    vecNumber :: DVec a -> Build a (DVec a)

    vecUnboxKey :: DVec a -> Build a (KVec a)

    -- | From a vector with only one segment, create a segmented
    -- version in which every value in the original segment inhabits
    -- its own segment.
    vecSegment :: DVec a -> Build a (DVec a)

    -- | Turn a vector with multiple vectors into a vector with only the unit
    -- segment.
    vecUnsegment :: DVec a -> Build a (DVec a)

    vecAggr :: N.NonEmpty AggrFun -> DVec a -> Build a (DVec a)
    vecAggrSeg :: AggrFun -> DVec a -> DVec a -> Build a (DVec a)

    vecWinFun :: WinFun -> FrameSpec -> DVec a -> Build a (DVec a)

    -- | Reverse each segment of a vector individually.
    vecReverse :: DVec a -> Build a (DVec a, SVec a)

    -- | Filter a vector by applying a scalar boolean predicate.
    vecSelect:: Expr -> DVec a -> Build a (DVec a, FVec a)

    -- | Per-segment sorting of a vector.
    vecSort :: [Expr] -> DVec a -> Build a (DVec a, SVec a)

    -- | Per-segment grouping of a vector
    vecGroup :: [Expr] -> DVec a -> Build a (DVec a, DVec a, SVec a)

    -- | The VL aggregation operator groups every segment of the input vector by the
    -- given columns and then performs the list of aggregations described by the
    -- second argument. The result vector has the same segment structure as the
    -- input vector since all segments are grouped individually. The output
    -- payload columns are the grouping columns followed by the aggregation
    -- results.
    vecGroupAggr :: [Expr] -> N.NonEmpty AggrFun -> DVec a -> Build a (DVec a)

    -- | Construct a new vector as the result of a list of scalar
    -- expressions per result column.
    vecProject :: [Expr] -> DVec a -> Build a (DVec a)

    vecReplicateNest :: DVec a -> DVec a -> Build a (DVec a, RVec a)

    vecReplicateScalar :: DVec a -> DVec a -> Build a (DVec a, RVec a)

    vecReplicateVector :: DVec a -> DVec a -> Build a (DVec a, RVec a)

    -- | Apply a sorting vector to a data vector
    vecAppSort   :: SVec a -> DVec a -> Build a (DVec a, SVec a)

    -- | Apply a filter vector to a data vector
    vecAppFilter :: FVec a -> DVec a -> Build a (DVec a, FVec a)

    -- | Apply a rekeying vector to a data vector
    vecAppKey    :: KVec a -> DVec a -> Build a (DVec a, KVec a)

    -- | Apply a replication vector to a data vector
    vecAppRep    :: RVec a -> DVec a -> Build a (DVec a, RVec a)

    vecUnboxSng :: DVec a -> DVec a -> Build a (DVec a, KVec a)

    vecAppend :: DVec a -> DVec a -> Build a (DVec a, KVec a, KVec a)

    -- | Align two vectors positionally. However, in contrast to
    -- 'vecZip', these are not arbitrary vectors, but vectors which
    -- are guaranteed to have the same length because they are
    -- operands to lifted operators.
    vecAlign :: DVec a -> DVec a -> Build a (DVec a)

    -- | Positionally align two vectors per segment: @map zip xss
    -- yss@.
    vecZip :: DVec a -> DVec a -> Build a (DVec a, KVec a, KVec a)

    vecCartProduct :: DVec a -> DVec a -> Build a (DVec a, RVec a, RVec a)
    vecThetaJoin :: L.JoinPredicate Expr -> DVec a -> DVec a -> Build a (DVec a, RVec a, RVec a)
    vecNestJoin :: L.JoinPredicate Expr -> DVec a -> DVec a -> Build a (DVec a, RVec a, RVec a)
    vecSemiJoin :: L.JoinPredicate Expr -> DVec a -> DVec a -> Build a (DVec a, FVec a)
    vecAntiJoin :: L.JoinPredicate Expr -> DVec a -> DVec a -> Build a (DVec a, FVec a)
    vecGroupJoin :: L.JoinPredicate Expr -> L.NE AggrFun -> DVec a -> DVec a -> Build a (DVec a)

    vecCombine :: DVec a -> DVec a -> DVec a -> Build a (DVec a, KVec a, KVec a)
