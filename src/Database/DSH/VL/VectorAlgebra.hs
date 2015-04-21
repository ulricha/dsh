{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Database.DSH.VL.VectorAlgebra where

import qualified Data.List.NonEmpty              as N
import           Database.DSH.Common.Lang
import           Database.DSH.Common.Type
import           Database.DSH.VL.Lang
import           Database.Algebra.Dag.Build

class VectorAlgebra a where
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
    vecLit :: [ScalarType] -> [[ScalarVal]] -> Build a (DVec a)

    -- | A reference to a database-resident table.
    vecTableRef :: String -> BaseTableSchema -> Build a (DVec a)

    -- | Eliminate duplicates
    vecUnique :: DVec a -> Build a (DVec a)

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

    vecUnboxKey :: DVec a -> Build a (KVec a)

    -- | From a vector with only one segment, create a segmented
    -- version in which every value in the original segment inhabits
    -- its own segment.
    vecSegment :: DVec a -> Build a (DVec a, DVec a)

    vecAggr :: AggrFun -> DVec a -> Build a (DVec a)
    vecAggrS :: AggrFun -> DVec a -> DVec a -> Build a (DVec a)

    vecWinFun :: WinFun -> FrameSpec -> DVec a -> Build a (DVec a)

    -- | Reverse a vector.
    vecReverse :: DVec a -> Build a (DVec a, SVec a)

    -- | Reverse each segment of a vector individually.
    vecReverseS :: DVec a -> Build a (DVec a, SVec a)

    -- | Filter a vector by applying a scalar boolean predicate.
    vecSelect:: Expr -> DVec a -> Build a (DVec a, FVec a)

    -- | Sort a vector
    vecSort :: [Expr] -> DVec a -> Build a (DVec a, SVec a)

    -- | Per-segment sorting of a vector.
    vecSortS :: [Expr] -> DVec a -> Build a (DVec a, SVec a)

    -- | Regular grouping of a vector
    vecGroup :: [Expr] -> DVec a -> Build a (DVec a, DVec a, SVec a)

    -- | Per-segment grouping of a vector
    vecGroupS :: [Expr] -> DVec a -> Build a (DVec a, DVec a, SVec a)

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
    vecDistLift :: DVec a -> DVec a -> Build a (DVec a, RVec a)

    -- | Apply a sorting vector to a data vector
    vecAppSort   :: SVec a -> DVec a -> Build a (DVec a, SVec a)

    -- | Apply a filter vector to a data vector
    vecAppFilter :: FVec a -> DVec a -> Build a (DVec a, FVec a)

    -- | Apply a rekeying vector to a data vector
    vecAppKey    :: KVec a -> DVec a -> Build a (DVec a, KVec a)

    -- | Apply a replication vector to a data vector
    vecAppRep    :: RVec a -> DVec a -> Build a (DVec a, RVec a)

    vecUnboxScalar :: (DVec a) -> (DVec a) -> Build a (DVec a)

    vecAppend :: DVec a -> DVec a -> Build a (DVec a, KVec a, KVec a)
    vecAppendS :: DVec a -> DVec a -> Build a (DVec a, KVec a, KVec a)

    -- | Align two vectors positionally. However, in contrast to
    -- 'vecZip', these are not arbitrary vectors, but vectors which
    -- are guaranteed to have the same length because they are
    -- operands to lifted operators.
    vecAlign :: DVec a -> DVec a -> Build a (DVec a)

    -- | Positionally align two vectors. Basically: @zip xs ys@
    vecZip :: (DVec a) -> DVec a -> Build a (DVec a, KVec a, KVec a)

    -- | Positionally align two vectors per segment: @map zip xss
    -- yss@.
    vecZipS :: DVec a -> DVec a -> Build a (DVec a, KVec a, KVec a)

    vecCartProduct :: DVec a -> DVec a -> Build a (DVec a, RVec a, RVec a)
    vecCartProductS :: DVec a -> DVec a -> Build a (DVec a, RVec a, RVec a)
    vecNestProduct :: DVec a -> DVec a -> Build a (DVec a, RVec a, RVec a)
    vecNestProductS :: DVec a -> DVec a -> Build a (DVec a, RVec a, RVec a)

    vecThetaJoin :: JoinPredicate Expr -> DVec a -> DVec a -> Build a (DVec a, RVec a, RVec a)
    vecNestJoin :: JoinPredicate Expr -> DVec a -> DVec a -> Build a (DVec a, RVec a, RVec a)
    vecThetaJoinS :: JoinPredicate Expr -> DVec a -> DVec a -> Build a (DVec a, RVec a, RVec a)
    vecNestJoinS :: JoinPredicate Expr -> DVec a -> DVec a -> Build a (DVec a, RVec a, RVec a)

    vecGroupJoin :: JoinPredicate Expr -> AggrFun -> DVec a -> DVec a -> Build a (DVec a)

    vecSemiJoin :: JoinPredicate Expr -> DVec a -> DVec a -> Build a (DVec a, FVec a)
    vecSemiJoinS :: JoinPredicate Expr -> DVec a -> DVec a -> Build a (DVec a, FVec a)

    vecAntiJoin :: JoinPredicate Expr -> DVec a -> DVec a -> Build a (DVec a, FVec a)
    vecAntiJoinS :: JoinPredicate Expr -> DVec a -> DVec a -> Build a (DVec a, FVec a)

    vecCombine :: DVec a -> DVec a -> DVec a -> Build a (DVec a, KVec a, KVec a)

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
