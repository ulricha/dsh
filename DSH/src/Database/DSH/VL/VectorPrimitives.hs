module Database.DSH.VL.VectorPrimitives where

import Database.DSH.VL.Data.DBVector
import Database.Algebra.VL.Data (VLType(), TypedColumn, Key, VLVal(), VecCompOp(), ISTransProj, Expr1, Expr2, Nat, AggrFun)

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
  singletonDescr :: GraphM r a DBV
  
  -- FIXME rename to litAtom
  constructLiteralValue :: [VLType] -> [VLVal] -> GraphM r a DBP
  -- FIXME rename to litTable
  constructLiteralTable :: [VLType] -> [[VLVal]] -> GraphM r a DBV
  tableRef :: String -> [TypedColumn] -> [Key] -> GraphM r a DBV

  -- FIXME rename to distinct
  unique :: DBV -> GraphM r a DBV
  uniqueL :: DBV -> GraphM r a DBV

  number :: DBV -> GraphM r a DBV
  numberL :: DBV -> GraphM r a DBV  

  descToRename :: DBV -> GraphM r a RenameVector
  segment :: DBV -> GraphM r a DBV
  unsegment :: DBV -> GraphM r a DBV
  
  -- FIXME combine into generic aggregate operator
  -- although: backend implementation can be quite different.
  vecSum :: VLType -> DBV -> GraphM r a DBP
  vecSumLift :: DBV -> DBV -> GraphM r a DBV
  -- Avg is unsafe! Empty lists will disappear, as average does not have a
  -- default value (in contrast to sum).
  vecAvgLift :: DBV -> DBV -> GraphM r a DBV
  lengthSeg :: DBV -> DBV -> GraphM r a DBV
  lengthA :: DBV -> GraphM r a DBP
  -- Avg is unsafe! Empty lists will disappear, as average does not have a
  -- default value (in contrast to sum).
  vecAvg :: DBV -> GraphM r a DBP
  vecMin :: DBV -> GraphM r a DBP
  vecMinLift :: DBV -> GraphM r a DBV
  vecMax :: DBV -> GraphM r a DBP
  vecMaxLift :: DBV -> GraphM r a DBV

  selectPos1 :: DBV -> VecCompOp -> Nat -> GraphM r a (DBV, RenameVector)
  selectPos1Lift :: DBV -> VecCompOp -> Nat -> GraphM r a (DBV, RenameVector)

  reverseA :: DBV -> GraphM r a (DBV, PropVector)
  reverseL :: DBV -> GraphM r a (DBV, PropVector)
  
  -- FIXME this operator is too specialized. Could be implemented with NOT, PROJECT
  -- and some operator that materializes positions.
  falsePositions :: DBV -> GraphM r a DBV

  selectExpr :: Expr1 -> DBV -> GraphM r a DBV

  projectRename :: ISTransProj -> ISTransProj -> DBV -> GraphM r a RenameVector

  vecProject :: [Expr1] -> DBV -> GraphM r a DBV
  vecProjectA :: [Expr1] -> DBP -> GraphM r a DBP
  
  groupByKey :: DBV -> DBV -> GraphM r a (DBV, DBV, PropVector)

  -- | The VL aggregation operator groups the input vector by the given columns
  -- and then performs the list of aggregations described by the second
  -- argument. The result is a flat vector, since all groups are reduced via
  -- aggregation.
  vecAggr :: [DBCol] -> [AggrFun] -> DBV -> GraphM r a DBV

  sortWith :: DBV -> DBV -> GraphM r a (DBV, PropVector)
  distPrim :: DBP -> DBV -> GraphM r a (DBV, PropVector)
  distDesc :: DBV -> DBV -> GraphM r a (DBV, PropVector)
  distLift :: DBV -> DBV -> GraphM r a (DBV, PropVector)
  -- | propRename uses a propagation vector to rename a vector (no filtering or reordering).
  propRename :: RenameVector -> DBV -> GraphM r a DBV
  -- | propFilter uses a propagation vector to rename and filter a vector (no reordering).
  propFilter :: RenameVector -> DBV -> GraphM r a (DBV, RenameVector)
  -- | propReorder uses a propagation vector to rename, filter and reorder a vector.
  propReorder :: PropVector -> DBV -> GraphM r a (DBV, PropVector)
  append :: DBV -> DBV -> GraphM r a (DBV, RenameVector, RenameVector)
  restrictVec :: DBV -> DBV -> GraphM r a (DBV, RenameVector)
  
  -- FIXME better name
  compExpr2 :: Expr2 -> DBP -> DBP -> GraphM r a DBP
  compExpr2L :: Expr2 -> DBV -> DBV -> GraphM r a DBV

  selectPos :: DBV -> VecCompOp -> DBP -> GraphM r a (DBV, RenameVector)
  selectPosLift :: DBV -> VecCompOp -> DBV -> GraphM r a (DBV, RenameVector)

  -- FIXME should go away when DBP is eliminated
  pairA :: DBP -> DBP -> GraphM r a DBP
  
  -- FIXME better name: zip
  pairL :: DBV -> DBV -> GraphM r a DBV

  -- FIXME better name: zipSeg
  zipL :: DBV -> DBV -> GraphM r a (DBV, RenameVector, RenameVector)

  cartProduct :: DBV -> DBV -> GraphM r a (DBV, PropVector, PropVector)
  cartProductL :: DBV -> DBV -> GraphM r a (DBV, PropVector, PropVector)

  equiJoin :: Expr1 -> Expr1 -> DBV -> DBV -> GraphM r a (DBV, PropVector, PropVector)
  equiJoinL :: Expr1 -> Expr1 -> DBV -> DBV -> GraphM r a (DBV, PropVector, PropVector)
  
  semiJoin :: Expr1 -> Expr1 -> DBV -> DBV -> GraphM r a (DBV, RenameVector)
  semiJoinL :: Expr1 -> Expr1 -> DBV -> DBV -> GraphM r a (DBV, RenameVector)

  antiJoin :: Expr1 -> Expr1 -> DBV -> DBV -> GraphM r a (DBV, RenameVector)
  antiJoinL :: Expr1 -> Expr1 -> DBV -> DBV -> GraphM r a (DBV, RenameVector)

  combineVec :: DBV -> DBV -> DBV -> GraphM r a (DBV, RenameVector, RenameVector)
  
