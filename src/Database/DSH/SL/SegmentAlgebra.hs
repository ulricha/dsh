{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies          #-}

module Database.DSH.SL.SegmentAlgebra where

import qualified Data.List.NonEmpty                as N
import           Database.Algebra.Dag.Build
import qualified Database.DSH.Common.Lang          as L
import           Database.DSH.Common.VectorLang

-- | This class defines the segment operators that need to be implemented by a
-- backend.
class SegmentAlgebra a where
    -- | Data Vector
    type SLDVec a

    -- | Re-Keying Vector
    type SLKVec a

    -- | Replication Vector
    type SLRVec a

    -- | Sorting Vector
    type SLSVec a

    -- | Filtering Vector
    type SLFVec a

    -- | A vector representing a literal list.
    vecLit :: PType -> VecSegs -> Build a (SLDVec a)

    -- | A reference to a database-resident table.
    vecTableRef :: String -> L.BaseTableSchema -> Build a (SLDVec a)

    -- | Perform duplicate elimination per segment.
    vecUnique :: SLDVec a -> Build a (SLDVec a)

    -- | /Materialize/ vector positions per segment. The operator adds
    -- an item column that contains the dense positions of the
    -- vector's elements in each segment.
    vecNumber :: SLDVec a -> Build a (SLDVec a)

    -- | Merge segments of an inner vector into the segment structure of the
    -- outer vector.
    vecMergeSeg :: SLDVec a -> SLDVec a -> Build a (SLDVec a)

    -- | From a vector with only one segment, create a segmented
    -- version in which every value in the original segment inhabits
    -- its own segment.
    vecSegment :: SLDVec a -> Build a (SLDVec a)

    -- | Turn a vector with multiple vectors into a vector with only the unit
    -- segment.
    vecUnsegment :: SLDVec a -> Build a (SLDVec a)

    vecFold :: AggrFun TExpr -> SLDVec a -> Build a (SLDVec a)

    vecWinFun :: WinFun TExpr -> FrameSpec -> SLDVec a -> Build a (SLDVec a)

    -- | Reverse each segment of a vector individually.
    vecReverse :: SLDVec a -> Build a (SLDVec a, SLSVec a)

    -- | Filter a vector by applying a scalar boolean predicate.
    vecSelect:: TExpr -> SLDVec a -> Build a (SLDVec a, SLFVec a)

    -- | Per-segment sorting of a vector.
    vecSort :: TExpr -> SLDVec a -> Build a (SLDVec a, SLSVec a)

    -- | Per-segment grouping of a vector
    vecGroup :: TExpr -> SLDVec a -> Build a (SLDVec a, SLDVec a, SLSVec a)

    -- | The VL aggregation operator groups every segment of the input vector by the
    -- given columns and then performs the list of aggregations described by the
    -- second argument. The result vector has the same segment structure as the
    -- input vector since all segments are grouped individually. The output
    -- payload columns are the grouping columns followed by the aggregation
    -- results.
    vecGroupAggr :: TExpr -> L.NE (AggrFun TExpr) -> SLDVec a -> Build a (SLDVec a)

    -- | Construct a new vector as the result of a list of scalar
    -- expressions per result column.
    vecProject :: TExpr -> SLDVec a -> Build a (SLDVec a)

    vecReplicateNest :: SLDVec a -> SLDVec a -> Build a (SLDVec a, SLRVec a)

    -- | Replicate the single scalar value in the left input vector to all elements
    -- of the right input vector.
    vecReplicateScalar :: SLDVec a -> SLDVec a -> Build a (SLDVec a, SLRVec a)

    -- | For each element of the right input vector create a corresponding segment
    -- with a copy of the left input vector.
    vecReplicateVector :: SLDVec a -> SLDVec a -> Build a (SLDVec a, SLRVec a)

    -- | Apply a sorting vector to a data vector
    vecAppSort   :: SLSVec a -> SLDVec a -> Build a (SLDVec a, SLSVec a)

    -- | Apply a filter vector to a data vector
    vecAppFilter :: SLFVec a -> SLDVec a -> Build a (SLDVec a, SLFVec a)

    -- | Apply a rekeying vector to a data vector
    vecAppKey    :: SLKVec a -> SLDVec a -> Build a (SLDVec a, SLKVec a)

    -- | Apply a replication vector to a data vector
    vecAppRep    :: SLRVec a -> SLDVec a -> Build a (SLDVec a, SLRVec a)

    vecUnboxSng :: SLDVec a -> SLDVec a -> Build a (SLDVec a, SLKVec a)
    vecUnboxDefault :: TExpr -> SLDVec a -> SLDVec a -> Build a (SLDVec a)

    vecAppend :: SLDVec a -> SLDVec a -> Build a (SLDVec a, SLKVec a, SLKVec a)

    -- | Align two vectors positionally. However, in contrast to
    -- 'vecZip', these are not arbitrary vectors, but vectors which
    -- are guaranteed to have the same length because they are
    -- operands to lifted operators.
    vecAlign :: SLDVec a -> SLDVec a -> Build a (SLDVec a)

    -- | Positionally align two vectors per segment: @map zip xss
    -- yss@.
    vecZip :: SLDVec a -> SLDVec a -> Build a (SLDVec a, SLRVec a, SLRVec a)

    vecCartProduct :: SLDVec a -> SLDVec a -> Build a (SLDVec a, SLRVec a, SLRVec a)
    vecThetaJoin :: L.JoinPredicate TExpr -> SLDVec a -> SLDVec a -> Build a (SLDVec a, SLRVec a, SLRVec a)
    vecNestJoin :: L.JoinPredicate TExpr -> SLDVec a -> SLDVec a -> Build a (SLDVec a, SLRVec a, SLRVec a)
    vecSemiJoin :: L.JoinPredicate TExpr -> SLDVec a -> SLDVec a -> Build a (SLDVec a, SLFVec a)
    vecAntiJoin :: L.JoinPredicate TExpr -> SLDVec a -> SLDVec a -> Build a (SLDVec a, SLFVec a)
    vecGroupJoin :: L.JoinPredicate TExpr -> L.NE (AggrFun TExpr) -> SLDVec a -> SLDVec a -> Build a (SLDVec a)

    vecCombine :: SLDVec a -> SLDVec a -> SLDVec a -> Build a (SLDVec a, SLKVec a, SLKVec a)
