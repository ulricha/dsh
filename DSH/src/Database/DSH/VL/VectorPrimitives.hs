module Database.DSH.VL.VectorPrimitives where

import qualified Data.List.NonEmpty as N
import           Database.DSH.Common.Lang
import           Database.DSH.VL.Data.DBVector
import           Database.DSH.VL.Lang

-- FIXME this should import a module from TableAlgebra which defines
-- common types like schema info and abstract column types.
import Database.Algebra.Pathfinder()

-- * Vector primitive constructor functions

{-

FIXME
consistent naming scheme:

- atom = A
- lifted is the standard case
- difference between lifted and segmented -> segmented S
- common prefix: vec. vl is reserved for the actual VL operators
-}

class VectorAlgebra a where
  singletonDescr :: GraphM r a DVec
  
  vecLit :: [VLType] -> [[VLVal]] -> GraphM r a DVec
  vecTableRef :: String -> [VLColumn] -> TableHints -> GraphM r a DVec

  vecUniqueS :: DVec -> GraphM r a DVec

  vecNumber :: DVec -> GraphM r a DVec
  vecNumberS :: DVec -> GraphM r a DVec  

  descToRename :: DVec -> GraphM r a RVec

  vecSegment :: DVec -> GraphM r a DVec
  vecUnsegment :: DVec -> GraphM r a DVec
  
  vecAggr :: AggrFun -> DVec -> GraphM r a DVec
  vecAggrS :: AggrFun -> DVec -> DVec -> GraphM r a DVec
  vecAggrNonEmpty :: N.NonEmpty AggrFun -> DVec -> GraphM r a DVec
  vecAggrNonEmptyS :: N.NonEmpty AggrFun -> DVec -> DVec -> GraphM r a DVec

  -- FIXME operator too specialized. should be implemented using number + select
  selectPos1 :: DVec -> ScalarBinOp -> Nat -> GraphM r a (DVec, RVec)
  selectPos1S :: DVec -> ScalarBinOp -> Nat -> GraphM r a (DVec, RVec)

  vecReverse :: DVec -> GraphM r a (DVec, PVec)
  vecReverseS :: DVec -> GraphM r a (DVec, PVec)
  
  vecSelect:: Expr1 -> DVec -> GraphM r a DVec

  vecSortSimple :: [Expr1] -> DVec -> GraphM r a (DVec, PVec)
  vecGroupSimple :: [Expr1] -> DVec -> GraphM r a (DVec, DVec, PVec)

  vecProject :: [Expr1] -> DVec -> GraphM r a DVec
  
  vecGroupBy :: DVec -> DVec -> GraphM r a (DVec, DVec, PVec)

  -- | The VL aggregation operator groups the input vector by the
  -- given columns and then performs the list of aggregations
  -- described by the second argument. The result is a flat vector,
  -- since all groups are reduced via aggregation. The operator
  -- operates segmented, i.e. always groups by descr first. This
  -- operator must be used with care: It does not determine the
  -- complete set of descr value to check for empty inner lists.
  vecGroupAggr :: [Expr1] -> N.NonEmpty AggrFun -> DVec -> GraphM r a DVec

  vecSort :: DVec -> DVec -> GraphM r a (DVec, PVec)
  -- FIXME is distprim really necessary? could maybe be replaced by distdesc
  vecDistPrim :: DVec -> DVec -> GraphM r a (DVec, PVec)
  vecDistDesc :: DVec -> DVec -> GraphM r a (DVec, PVec)
  vecAlign    :: DVec -> DVec -> GraphM r a (DVec, PVec)

  -- | propRename uses a propagation vector to rename a vector (no filtering or reordering).
  vecPropRename :: RVec -> DVec -> GraphM r a DVec
  -- | propFilter uses a propagation vector to rename and filter a vector (no reordering).
  vecPropFilter :: RVec -> DVec -> GraphM r a (DVec, RVec)
  -- | propReorder uses a propagation vector to rename, filter and reorder a vector.
  vecPropReorder :: PVec -> DVec -> GraphM r a (DVec, PVec)
  vecAppend :: DVec -> DVec -> GraphM r a (DVec, RVec, RVec)
  vecRestrict :: DVec -> DVec -> GraphM r a (DVec, RVec)
  
  vecBinExpr :: Expr2 -> DVec -> DVec -> GraphM r a DVec

  -- FIXME could be implemented using number and select
  selectPos :: DVec -> ScalarBinOp -> DVec -> GraphM r a (DVec, RVec)
  selectPosS :: DVec -> ScalarBinOp -> DVec -> GraphM r a (DVec, RVec)

  -- FIXME better name: zip
  vecZip :: DVec -> DVec -> GraphM r a DVec

  -- FIXME better name: zipSeg
  vecZipS :: DVec -> DVec -> GraphM r a (DVec, RVec, RVec)

  vecCartProduct :: DVec -> DVec -> GraphM r a (DVec, PVec, PVec)
  vecCartProductS :: DVec -> DVec -> GraphM r a (DVec, PVec, PVec)
  vecNestProductS :: DVec -> DVec -> GraphM r a (DVec, PVec)

  vecThetaJoin :: JoinPredicate Expr1 -> DVec -> DVec -> GraphM r a (DVec, PVec, PVec)
  vecThetaJoinS :: JoinPredicate Expr1 -> DVec -> DVec -> GraphM r a (DVec, PVec, PVec)
  vecNestJoinS :: JoinPredicate Expr1 -> DVec -> DVec -> GraphM r a (DVec, PVec)
  
  vecSemiJoin :: JoinPredicate Expr1 -> DVec -> DVec -> GraphM r a (DVec, RVec)
  vecSemiJoinS :: JoinPredicate Expr1 -> DVec -> DVec -> GraphM r a (DVec, RVec)

  vecAntiJoin :: JoinPredicate Expr1 -> DVec -> DVec -> GraphM r a (DVec, RVec)
  vecAntiJoinS :: JoinPredicate Expr1 -> DVec -> DVec -> GraphM r a (DVec, RVec)

  vecCombine :: DVec -> DVec -> DVec -> GraphM r a (DVec, RVec, RVec)

  vecReshape :: Integer -> DVec -> GraphM r a (DVec, DVec)
  
  -- reshapeS can be computed only on the inner vector. As its result
  -- is one list nesting level deeper, it computes the new innermost
  -- vector from the old inner vector and then derives from that a
  -- 'middle' descriptor vector which represents lists at nesting
  -- depth 1.
  vecReshapeS :: Integer -> DVec -> GraphM r a (DVec, DVec)

  vecTranspose :: DVec -> GraphM r a (DVec, DVec)
  vecTransposeS :: DVec -> DVec -> GraphM r a (DVec, DVec)
  
