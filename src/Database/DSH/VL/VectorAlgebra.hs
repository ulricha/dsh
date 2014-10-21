{-# LANGUAGE MultiParamTypeClasses #-}

module Database.DSH.VL.VectorAlgebra where

import qualified Data.List.NonEmpty              as N
import           Database.DSH.Common.Lang
import           Database.DSH.VL.Vector
import           Database.DSH.VL.Lang
import           Database.Algebra.Dag.Build

class VectorAlgebra v a where
    -- | A vector with one segment
    singletonDescr :: Build a v

    -- | A vector representing a literal list.
    vecLit :: [ScalarType] -> [[VLVal]] -> Build a v

    -- | A reference to a database-resident table.
    vecTableRef :: String -> [VLColumn] -> TableHints -> Build a v

    -- | Perform duplicate elimination per segment.
    vecUniqueS :: v -> Build a v

    -- | /Materialize/ vector positions. The operator adds an item
    -- column that contains the dense positions of the vector's
    -- elements.
    vecNumber :: v -> Build a v

    -- | /Materialize/ vector positions per segment. The operator adds
    -- an item column that contains the dense positions of the
    -- vector's elements in each segment.
    vecNumberS :: v -> Build a v

    descToRename :: v -> Build a RVec

    -- | From a vector with only one segment, create a segmented
    -- version in which every value in the original segment inhabits
    -- its own segment.
    vecSegment :: v -> Build a v

    vecUnsegment :: v -> Build a v

    vecAggr :: AggrFun -> v -> Build a v
    vecAggrS :: AggrFun -> v -> v -> Build a v
    vecAggrNonEmpty :: N.NonEmpty AggrFun -> v -> Build a v
    vecAggrNonEmptyS :: N.NonEmpty AggrFun -> v -> Build a v

    vecWinFun :: WinFun -> FrameSpec -> v -> Build a v

    -- | SelectPos filters a vector positionally as specified by the
    -- comparison operator and the position value from the right
    -- input. Next to the filtered value vector it produces two rename
    -- vectors:
    --
    -- * Mapping old to new positions (for re-aligning inner vectors)
    -- * Mapping old positions to segment descriptors (for unboxing one
    -- inner segment)
    -- FIXME should be restricted to RelOp!
    vecSelectPos :: v -> ScalarBinOp -> v -> Build a (v, RVec, RVec)

    -- | Filter a vector positionally /by segment/. The right input
    -- vector provides a position offset /for each segment/. The
    -- operator produces the same triple of vectors as its non-segmented
    -- variant.
    vecSelectPosS :: v -> ScalarBinOp -> v -> Build a (v, RVec, RVec)

    -- | Filter a vector positionally on a /constant/ position.
    vecSelectPos1 :: v -> ScalarBinOp -> Int -> Build a (v, RVec, RVec)

    -- | Filter a vector positionally based on a /constant
    -- position/. The operator filters by segment, but the constant
    -- position argument is the same for all segments.
    vecSelectPos1S :: v -> ScalarBinOp -> Int -> Build a (v, RVec, RVec)

    -- | Reverse a vector.
    vecReverse :: v -> Build a (v, PVec)

    -- | Reverse each segment of a vector individually.
    vecReverseS :: v -> Build a (v, PVec)

    -- | Filter a vector by applying a scalar boolean predicate.
    vecSelect:: Expr -> v -> Build a (v, RVec)

    -- | General vector sorting (segmented). The sorting key is
    -- provided by the first input vector.
    vecSortS :: v -> v -> Build a (v, PVec)

    -- | Specialized variant of sorting: The sorting key is provided
    -- by a scalar expression.
    vecSortScalarS :: [Expr] -> v -> Build a (v, PVec)

    vecGroup :: v -> v -> Build a (v, v, PVec)
    vecGroupScalarS :: [Expr] -> v -> Build a (v, v, PVec)

    -- | The VL aggregation operator groups the input vector by the
    -- given columns and then performs the list of aggregations
    -- described by the second argument. The result is a flat vector,
    -- since all groups are reduced via aggregation. The operator
    -- operates segmented, i.e. always groups by descr first. This
    -- operator must be used with care: It does not determine the
    -- complete set of descr value to check for empty inner lists.
    -- The output payload columns are the grouping columns followed by
    -- the aggregation results.
    vecGroupAggr :: [Expr] -> N.NonEmpty AggrFun -> v -> Build a v


    -- | Construct a new vector as the result of a list of scalar
    -- expressions per result column.
    vecProject :: [Expr] -> v -> Build a v

    -- FIXME is distprim really necessary? could maybe be replaced by distdesc
    vecDistPrim :: v -> v -> Build a (v, PVec)
    vecDistDesc :: v -> v -> Build a (v, PVec)
    vecDistLift :: v -> v -> Build a (v, PVec)

    -- | propRename uses a propagation vector to rename a vector (no
    -- filtering or reordering).
    vecPropRename :: RVec -> v -> Build a v

    -- | propFilter uses a propagation vector to rename and filter a
    -- vector (no reordering).
    vecPropFilter :: RVec -> v -> Build a (v, RVec)

    -- | propReorder uses a propagation vector to rename, filter and
    -- reorder a vector.
    vecPropReorder :: PVec -> v -> Build a (v, PVec)

    -- | Specialized unbox operator that merges DescrToRename
    -- and PropRename. It takes an inner and outer vector, and
    -- pulls the segment that is referenced by the outer vector
    -- into the outer segment. Notice that there must be
    -- /exactly one/ segment referenced by the outer
    -- vector. Inner segments that are not referenced are
    -- silently discarded.
    --
    -- Output: @(DVec r, RVec)@
    vecUnboxNested :: RVec -> v -> Build a (v, RVec)

    vecUnboxScalar :: v -> v -> Build a v

    vecAppend :: v -> v -> Build a (v, RVec, RVec)
    vecAppendS :: v -> v -> Build a (v, RVec, RVec)

    -- | Align two vectors positionally. However, in contrast to
    -- 'vecZip', these are not arbitrary vectors, but vectors which
    -- are guaranteed to have the same length because they are
    -- operands to lifted operators.
    vecAlign :: v -> v -> Build a v

    -- | Positionally align two vectors. Basically: @zip xs ys@
    vecZip :: v -> v -> Build a v

    -- | Positionally align two vectors per segment: @map zip xss
    -- yss@.
    vecZipS :: v -> v -> Build a (v, RVec, RVec)

    vecCartProduct :: v -> v -> Build a (v, PVec, PVec)
    vecCartProductS :: v -> v -> Build a (v, PVec, PVec)
    vecNestProductS :: v -> v -> Build a (v, PVec)

    vecThetaJoin :: JoinPredicate Expr -> v -> v -> Build a (v, PVec, PVec)
    vecNestJoin :: JoinPredicate Expr -> v -> v -> Build a (v, PVec, PVec)
    vecThetaJoinS :: JoinPredicate Expr -> v -> v -> Build a (v, PVec, PVec)
    vecNestJoinS :: JoinPredicate Expr -> v -> v -> Build a (v, PVec)

    vecSemiJoin :: JoinPredicate Expr -> v -> v -> Build a (v, RVec)
    vecSemiJoinS :: JoinPredicate Expr -> v -> v -> Build a (v, RVec)

    vecAntiJoin :: JoinPredicate Expr -> v -> v -> Build a (v, RVec)
    vecAntiJoinS :: JoinPredicate Expr -> v -> v -> Build a (v, RVec)

    vecCombine :: v -> v -> v -> Build a (v, RVec, RVec)

    -- | Experimental: @reshape m@ partitions a vector of length @n*m@
    -- into @n@ vectors of length @m@.
    --
    -- reshapeS can be computed only on the inner vector. As its
    -- result is one list nesting level deeper, it computes the new
    -- innermost vector from the old inner vector and then derives
    -- from that a 'middle' descriptor vector which represents lists
    -- at nesting depth 1.
    vecReshape :: Integer -> v -> Build a (v, v)

    -- | Experimental: segmented version of reshape.
    vecReshapeS :: Integer -> v -> Build a (v, v)

    -- | Experimental: Matrix transposition
    vecTranspose :: v -> Build a (v, v)

    -- | Experimental: Segmented matrix transposition
    vecTransposeS :: v -> v -> Build a (v, v)

