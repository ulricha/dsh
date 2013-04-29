module Database.DSH.Flattening.VL.VectorPrimitives where

import Database.DSH.Flattening.VL.Data.DBVector
import Database.Algebra.VL.Data (VLType(), TypedColumn, Key, VLVal(), VecCompOp(), ISTransProj, DescrProj, PosProj, PayloadProj, Expr1, Expr2, Nat, AggrFun)

-- FIXME this should import a module from TableAlgebra which defines
-- common types like schema info and abstract column types.
import Database.Algebra.Pathfinder()

-- * Vector primitive constructor functions

class VectorAlgebra a where
  singletonDescr :: GraphM r a DescrVector
  constructLiteralValue :: [VLType] -> [VLVal] -> GraphM r a DBP
  constructLiteralTable :: [VLType] -> [[VLVal]] -> GraphM r a DBV
  tableRef :: String -> [TypedColumn] -> [Key] -> GraphM r a DBV

  unique :: DBV -> GraphM r a DBV
  uniqueL :: DBV -> GraphM r a DBV
  notPrim :: DBP -> GraphM r a DBP
  notVec :: DBV -> GraphM r a DBV
  lengthA :: DescrVector -> GraphM r a DBP
  descToRename :: DescrVector -> GraphM r a RenameVector
  toDescr :: DBV -> GraphM r a DescrVector
  segment :: DBV -> GraphM r a DBV
  unsegment :: DBV -> GraphM r a DBV
  vecSum :: VLType -> DBV -> GraphM r a DBP
  -- Avg is unsafe! Empty lists will disappear, as average does not have a
  -- default value (in contrast to sum).
  vecAvg :: DBV -> GraphM r a DBP
  vecMin :: DBV -> GraphM r a DBP
  vecMinLift :: DBV -> GraphM r a DBV
  vecMax :: DBV -> GraphM r a DBP
  vecMaxLift :: DBV -> GraphM r a DBV
  selectPos1 :: DBV -> VecCompOp -> Nat -> GraphM r a (DBV, RenameVector)
  selectPos1Lift :: DBV -> VecCompOp -> Nat -> GraphM r a (DBV, RenameVector)
  projectL :: DBV -> [DBCol] -> GraphM r a DBV
  projectA :: DBP -> [DBCol] -> GraphM r a DBP
  
  -- FIXME this should be a generic cast operator
  integerToDoubleA :: DBP -> GraphM r a DBP
  integerToDoubleL :: DBV -> GraphM r a DBV
  reverseA :: DBV -> GraphM r a (DBV, PropVector)
  reverseL :: DBV -> GraphM r a (DBV, PropVector)
  falsePositions :: DBV -> GraphM r a DBV
  selectExpr :: Expr1 -> DBV -> GraphM r a DBV
  projectRename :: ISTransProj -> ISTransProj -> DBV -> GraphM r a RenameVector
  projectAdmin :: DescrProj -> PosProj -> DBV -> GraphM r a DBV
  projectPayload :: [PayloadProj] -> DBV -> GraphM r a DBV
  compExpr1 :: Expr1 -> DBV -> GraphM r a DBV

  groupByKey :: DBV -> DBV -> GraphM r a (DBV, DBV, PropVector)

  -- | The VL aggregation operator groups the input vector by the given columns
  -- and then performs the list of aggregations described by the second
  -- argument. The result is a flat vector, since all groups are reduced via
  -- aggregation.
  vecAggr :: [DBCol] -> [AggrFun] -> DBV -> GraphM r a DBV
  sortWith :: DBV -> DBV -> GraphM r a (DBV, PropVector)
  lengthSeg :: DescrVector -> DescrVector -> GraphM r a DBV
  distPrim :: DBP -> DescrVector -> GraphM r a (DBV, PropVector)
  distDesc :: DBV -> DescrVector -> GraphM r a (DBV, PropVector)
  distLift :: DBV -> DescrVector -> GraphM r a (DBV, PropVector)
  -- | propRename uses a propagation vector to rename a vector (no filtering or reordering).
  propRename :: RenameVector -> DBV -> GraphM r a DBV
  -- | propFilter uses a propagation vector to rename and filter a vector (no reordering).
  propFilter :: RenameVector -> DBV -> GraphM r a (DBV, RenameVector)
  -- | propReorder uses a propagation vector to rename, filter and reorder a vector.
  propReorder :: PropVector -> DBV -> GraphM r a (DBV, PropVector)
  append :: DBV -> DBV -> GraphM r a (DBV, RenameVector, RenameVector)
  restrictVec :: DBV -> DBV -> GraphM r a (DBV, RenameVector)
  compExpr2 :: Expr2 -> DBP -> DBP -> GraphM r a DBP
  compExpr2L :: Expr2 -> DBV -> DBV -> GraphM r a DBV
  vecSumLift :: DescrVector -> DBV -> GraphM r a DBV
  -- Avg is unsafe! Empty lists will disappear, as average does not have a
  -- default value (in contrast to sum).
  vecAvgLift :: DescrVector -> DBV -> GraphM r a DBV
  selectPos :: DBV -> VecCompOp -> DBP -> GraphM r a (DBV, RenameVector)
  selectPosLift :: DBV -> VecCompOp -> DBV -> GraphM r a (DBV, RenameVector)
  pairA :: DBP -> DBP -> GraphM r a DBP
  pairL :: DBV -> DBV -> GraphM r a DBV
  zipL :: DBV -> DBV -> GraphM r a (DBV, RenameVector, RenameVector)
  cartProduct :: DBV -> DBV -> GraphM r a (DBV, PropVector, PropVector)
  thetaJoin :: Expr1 -> DBV -> DBV -> GraphM r a (DBV, DBV)

  combineVec :: DBV -> DBV -> DBV -> GraphM r a (DBV, RenameVector, RenameVector)
  
