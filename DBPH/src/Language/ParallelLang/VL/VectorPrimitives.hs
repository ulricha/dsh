module Language.ParallelLang.VL.VectorPrimitives where

import qualified Language.ParallelLang.Common.Data.Type as Ty
import Language.ParallelLang.Common.Data.Val
import Language.ParallelLang.FKL.Data.FKL
import Language.ParallelLang.Common.Data.Op
import Language.ParallelLang.VL.Data.DBVector

import Language.ParallelLang.VL.Data.Vector

-- FIXME this should import a module from TableAlgebra which defines 
-- common types like schema info and abstract column types.
import Database.Algebra.Pathfinder()

-- * Vector primitive constructor functions

data AuxColumn = Pos
            | Pos'
            | Pos''
            | Pos'''
            | Descr
            | Descr'
            | Descr''
            | PosOld
            | PosNew
            | OrdCol
            | ResCol
            | TmpCol
            | TmpCol'
            | Item
            | Item'

data AbstractColumn = DataCol DataColumn
                    | AuxCol AuxColumn

type TypedAbstractColumn t = (AbstractColumn, t)

class VectorAlgebra a where
  groupBy :: DBV -> DBV -> Graph a (DescrVector, DBV, PropVector)
  sortWith :: DBV -> DBV -> Graph a (DBV, PropVector)
  notPrim :: DBP -> Graph a DBP
  notVec :: DBV -> Graph a DBV
  lengthA :: DescrVector -> Graph a DBP
  lengthSeg :: DescrVector -> DescrVector -> Graph a DBV
  descToRename :: DescrVector -> Graph a RenameVector
  toDescr :: DBV -> Graph a DescrVector
  distPrim :: DBP -> DescrVector -> Graph a (DBV, PropVector)
  distDesc :: DBV -> DescrVector -> Graph a (DBV, PropVector)
  distLift :: DBV -> DescrVector -> Graph a (DBV, PropVector)
  -- | propRename uses a propagation vector to rename a vector (no filtering or reordering).
  propRename :: RenameVector -> DBV -> Graph a DBV
  -- | propFilter uses a propagation vector to rename and filter a vector (no reordering).
  propFilter :: RenameVector -> DBV -> Graph a (DBV, RenameVector)
  -- | propReorder uses a propagation vector to rename, filter and reorder a vector.
  propReorder :: PropVector -> DBV -> Graph a (DBV, PropVector)
  singletonDescr :: Graph a DescrVector
  append :: DBV -> DBV -> Graph a (DBV, RenameVector, RenameVector)
  segment :: DBV -> Graph a DBV
  restrictVec :: DBV -> DBV -> Graph a (DBV, RenameVector)
  combineVec :: DBV -> DBV -> DBV -> Graph a (DBV, RenameVector, RenameVector)
  constructLiteral :: Ty.Type -> Val -> Graph a Plan
  tableRef :: String -> [TypedColumn] -> [Key] -> Graph a Plan
  binOp :: Oper -> DBP -> DBP -> Graph a DBP
  binOpL :: Oper -> DBV -> DBV -> Graph a DBV
  vecSum :: Ty.Type -> DBV -> Graph a DBP
  vecSumLift :: DescrVector -> DBV -> Graph a DBV
  selectPos :: DBV -> Oper -> Plan -> Graph a (DBV, RenameVector)
  selectPosLift :: DBV -> Oper -> DBV -> Graph a (DBV, RenameVector)
  projectL :: DBV -> [DBCol] -> Graph a DBV
  projectA :: DBP -> [DBCol] -> Graph a DBP
  zipA :: DBP -> DBP -> Graph a DBP
  zipL :: DBV -> DBV -> Graph a DBV