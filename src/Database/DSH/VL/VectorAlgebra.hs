{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Database.DSH.VL.VectorAlgebra where

import qualified Data.List.NonEmpty              as N
import           Database.DSH.Common.Lang
import           Database.DSH.Common.Type
import           Database.DSH.Common.Vector
import           Database.DSH.VL.Lang
import           Database.Algebra.Dag.Build

class VectorAlgebra a where
    type DVec a

    -- | A vector with one segment
    singletonDescr :: Build a (DVec a)

    -- | A vector representing a literal list.
    vecLit :: [ScalarType] -> [[ScalarVal]] -> Build a (DVec a)

    -- | A reference to a database-resident table.
    vecTableRef :: String -> BaseTableSchema -> Build a (DVec a)

    -- | Perform duplicate elimination per segment.
    vecUniqueS :: DVec a -> Build a (DVec a)

    -- | /Materialize/ vector positions. The operator adds an item
    -- column that contains the dense positions of the vector's
    -- elements.
    vecNumber :: DVec a -> Build a (DVec a)

    -- | /Materialize/ vector positions per segment. The operator adds
    -- an item column that contains the dense positions of the
    -- vector's elements in each segment.
    vecNumberS :: DVec a -> Build a (DVec a)

    descToRename :: DVec a -> Build a RVec

    -- | From a vector with only one segment, create a segmented
    -- version in which every value in the original segment inhabits
    -- its own segment.
    vecSegment :: DVec a -> Build a (DVec a)

    vecUnsegment :: DVec a -> Build a (DVec a)

    vecAggr :: AggrFun -> DVec a -> Build a (DVec a)
    vecAggrS :: AggrFun -> DVec a -> DVec a -> Build a (DVec a)
    vecAggrNonEmpty :: N.NonEmpty AggrFun -> DVec a -> Build a (DVec a)
    vecAggrNonEmptyS :: N.NonEmpty AggrFun -> DVec a -> Build a (DVec a)

    vecWinFun :: WinFun -> FrameSpec -> DVec a -> Build a (DVec a)

    -- | SelectPos filters a vector positionally as specified by the
    -- comparison operator and the position value from the right
    -- input. Next to the filtered value vector it produces two rename
    -- vectors:
    --
    -- * Mapping old to new positions (for re-aligning inner vectors)
    -- * Mapping old positions to segment descriptors (for unboxing one
    -- inner segment)
    -- FIXME should be restricted to RelOp!
    vecSelectPos :: DVec a -> ScalarBinOp -> DVec a -> Build a (DVec a, RVec, RVec)

    -- | Filter a vector positionally /by segment/. The right input
    -- vector provides a position offset /for each segment/. The
    -- operator produces the same triple of vectors as its non-segmented
    -- variant.
    vecSelectPosS :: DVec a -> ScalarBinOp -> DVec a -> Build a (DVec a, RVec, RVec)

    -- | Filter a vector positionally on a /constant/ position.
    vecSelectPos1 :: DVec a -> ScalarBinOp -> Int -> Build a (DVec a, RVec, RVec)

    -- | Filter a vector positionally based on a /constant
    -- position/. The operator filters by segment, but the constant
    -- position argument is the same for all segments.
    vecSelectPos1S :: DVec a -> ScalarBinOp -> Int -> Build a (DVec a, RVec, RVec)

    -- | Reverse a vector.
    vecReverse :: DVec a -> Build a (DVec a, PVec)

    -- | Reverse each segment of a vector individually.
    vecReverseS :: DVec a -> Build a (DVec a, PVec)

    -- | Filter a vector by applying a scalar boolean predicate.
    vecSelect:: Expr -> DVec a -> Build a (DVec a, RVec)

    -- | Sort a vector
    vecSort :: [Expr] -> DVec a -> Build a (DVec a, PVec)

    -- | Per-segment sorting of a vector.
    vecSortS :: [Expr] -> DVec a -> Build a (DVec a, PVec)

    -- | Regular grouping of a vector
    vecGroup :: [Expr] -> DVec a -> Build a (DVec a, DVec a, PVec)

    -- | Per-segment grouping of a vector
    vecGroupS :: [Expr] -> DVec a -> Build a (DVec a, DVec a, PVec)

    -- | The VL aggregation operator groups the input vector by the
    -- given columns and then performs the list of aggregations
    -- described by the second argument. The result is a flat vector,
    -- since all groups are reduced via aggregation. The operator
    -- operates segmented, i.e. always groups by descr first. This
    -- operator must be used with care: It does not determine the
    -- complete set of descr value to check for empty inner lists.
    -- The output payload columns are the grouping columns followed by
    -- the aggregation results.
    vecGroupAggr :: [Expr] -> N.NonEmpty AggrFun -> DVec a -> Build a (DVec a)


    -- | Construct a new vector as the result of a list of scalar
    -- expressions per result column.
    vecProject :: [Expr] -> DVec a -> Build a (DVec a)

    -- FIXME is distprim really necessary? could maybe be replaced by distdesc
    vecDistLift :: DVec a -> DVec a -> Build a (DVec a, PVec)

    -- | propRename uses a propagation (DVec a)ector to rename a vector (no
    -- filtering or reordering).
    vecPropRename :: RVec -> DVec a -> Build a (DVec a)

    -- | propFilter uses a propagation vector to rename and filter a
    -- vector (no reordering).
    vecPropFilter :: RVec -> DVec a -> Build a (DVec a, RVec)

    -- | propReorder uses a propagation vector to rename, filter and
    -- reorder a vector.
    vecPropReorder :: PVec -> DVec a -> Build a (DVec a, PVec)

    -- | Specialized unbox operator that merges DescrToRename
    -- and PropRename. It takes an inner and outer vector, and
    -- pulls the segment that is referenced by the outer vector
    -- into the outer segment. Notice that there must be
    -- /exactly one/ segment referenced by the outer
    -- vector. Inner segments that are not referenced are
    -- silently discarded.
    --
    -- Output: @(DVec r, RVec)@
    vecUnboxNested :: RVec -> DVec a -> Build a (DVec a, RVec)

    vecUnboxScalar :: (DVec a) -> (DVec a) -> Build a (DVec a)

    vecAppend :: DVec a -> DVec a -> Build a (DVec a, RVec, RVec)
    vecAppendS :: DVec a -> DVec a -> Build a (DVec a, RVec, RVec)

    -- | Align two vectors positionally. However, in contrast to
    -- 'vecZip', these are not arbitrary vectors, but vectors which
    -- are guaranteed to have the same length because they are
    -- operands to lifted operators.
    vecAlign :: DVec a -> DVec a -> Build a (DVec a)

    -- | Positionally align two vectors. Basically: @zip xs ys@
    vecZip :: (DVec a) -> DVec a -> Build a (DVec a)

    -- | Positionally align two vectors per segment: @map zip xss
    -- yss@.
    vecZipS :: DVec a -> DVec a -> Build a (DVec a, RVec, RVec)

    vecCartProduct :: DVec a -> DVec a -> Build a (DVec a, PVec, PVec)
    vecCartProductS :: DVec a -> DVec a -> Build a (DVec a, PVec, PVec)
    vecNestProduct :: DVec a -> DVec a -> Build a (DVec a, PVec, PVec)
    -- FIXME inner result vector contains the outer values. Produce a
    -- propagation vector to align the layout.
    vecNestProductS :: DVec a -> DVec a -> Build a (DVec a, PVec)

    vecThetaJoin :: JoinPredicate Expr -> DVec a -> DVec a -> Build a (DVec a, PVec, PVec)
    vecNestJoin :: JoinPredicate Expr -> DVec a -> DVec a -> Build a (DVec a, PVec, PVec)
    vecThetaJoinS :: JoinPredicate Expr -> DVec a -> DVec a -> Build a (DVec a, PVec, PVec)
    vecNestJoinS :: JoinPredicate Expr -> DVec a -> DVec a -> Build a (DVec a, PVec)

    vecGroupJoin :: JoinPredicate Expr -> AggrFun -> DVec a -> DVec a -> Build a (DVec a)

    vecSemiJoin :: JoinPredicate Expr -> DVec a -> DVec a -> Build a (DVec a, RVec)
    vecSemiJoinS :: JoinPredicate Expr -> DVec a -> DVec a -> Build a (DVec a, RVec)

    vecAntiJoin :: JoinPredicate Expr -> DVec a -> DVec a -> Build a (DVec a, RVec)
    vecAntiJoinS :: JoinPredicate Expr -> DVec a -> DVec a -> Build a (DVec a, RVec)

    vecCombine :: DVec a -> DVec a -> DVec a -> Build a (DVec a, RVec, RVec)

    -- | Experimental: @reshape m@ partitions a vector of length @n*m@
    -- into @n@ vectors of length @m@.
    --
    -- reshapeS can be computed only on the inner vector. As its
    -- result is one list nesting level deeper, it computes the new
    -- innermost vector from the old inner vector and then derives
    -- from that a 'middle' descriptor vector which represents lists
    -- at nesting depth 1.
    vecReshape :: Integer -> DVec a -> Build a (DVec a, DVec a)

    -- | Experimental: segmented version of reshape.
    vecReshapeS :: Integer -> DVec a -> Build a (DVec a, DVec a)

    -- | Experimental: Matrix transposition
    vecTranspose :: DVec a -> Build a (DVec a, DVec a)

    -- | Experimental: Segmented matrix transposition
    vecTransposeS :: DVec a -> DVec a -> Build a (DVec a, DVec a)
