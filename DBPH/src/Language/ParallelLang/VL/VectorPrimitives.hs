module Language.ParallelLang.VL.VectorPrimitives where

import qualified Language.ParallelLang.Common.Data.Type as Ty
import Language.ParallelLang.Common.Data.Val
import Language.ParallelLang.FKL.Data.FKL
import Language.ParallelLang.Common.Data.Op
import Language.ParallelLang.VL.Data.DBVector

import Control.Applicative
import Language.ParallelLang.VL.Data.Vector

-- import Database.Algebra.Dag.Builder

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
  -- notA :: Plan -> Graph a Plan
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
--  restrictVec :: Plan -> Plan -> Graph a (Plan, RenameVector)
--  combineVec :: Plan -> Plan -> Plan -> Graph a (Plan, RenameVector, RenameVector)
--  bPermuteVec :: Plan -> Plan -> Graph a (Plan, PropVector)
  constructLiteral :: Ty.Type -> Val -> Graph a Plan
--  tableRef :: String -> [TypedColumn] -> [Key] -> Graph a Plan
--  emptyVector :: Maybe Ty.Type -> Graph a Plan
  binOp :: Oper -> DBP -> DBP -> Graph a DBP
  binOpL :: Oper -> DBV -> DBV -> Graph a DBV
  ifPrimList :: DBP -> DBV -> DBV -> Graph a DBV
  vecSum :: Ty.Type -> DBV -> Graph a DBP
  vecSumLift :: DescrVector -> DBV -> Graph a DBV
--  empty :: Plan -> Graph a Plan
--  emptyLift :: Plan -> Plan -> Graph a Plan
  selectPos :: DBV -> Oper -> Plan -> Graph a (DBV, RenameVector)
  selectPosLift :: DBV -> Oper -> DBV -> Graph a (DBV, RenameVector)
  projectL :: DBV -> [DBCol] -> Graph a DBV
  projectA :: DBP -> [DBCol] -> Graph a DBP

-- some purely compile time functions which involve no algebra code generation and 
-- are therefore the same for all instances of VectorAlgebra

concatV :: Plan -> Graph a Plan
concatV (ValueVector (Nest q lyt) _) = return $ ValueVector lyt q
concatV (AClosure n v l fvs x f1 f2) | l > 1 = AClosure n <$> (concatV v) 
                                                             <*> pure (l - 1) 
                                                             <*> (mapM (\(y, val) -> do
                                                                                        val' <- concatV val
                                                                                        return (y, val')) fvs)
                                                             <*> pure x <*> pure f1 <*> pure f2
concatV e                  = error $ "Not supported by concatV: " ++ show e


isValueVector :: Plan -> Bool
isValueVector = undefined
{-isValueVector (ValueVector _) = True
isValueVector _               = False -}

attachV :: Plan -> Plan -> Plan
attachV = undefined
{-attachV (DescrVector q1) e2 = NestedVector q1 e2
attachV _ _ = error "attachVPF: Should not be possible" -}

singletonVec :: VectorAlgebra a => Plan -> Graph a Plan
singletonVec (ValueVector lyt q) = do
                                    (DescrVector d) <- singletonDescr
                                    return $ ValueVector (Nest q lyt) d
                
singletonPrim :: VectorAlgebra a => Plan -> Graph a Plan
singletonPrim (PrimVal lyt q1) = return $ ValueVector lyt q1
singletonPrim _ = error "singletonPrim: Should not be possible"

                    
tagVector :: String -> Plan -> Graph a Plan
tagVector = undefined
{-
tagVector s (PairVector e1 e2) = PairVector <$> tagVector s e1 <*> tagVector s e2
tagVector s (DescrVector q) = DescrVector <$> tag s q
tagVector s (ValueVector q) = ValueVector <$> tag s q
tagVector s (PrimVal q) = PrimVal <$> tag s q
tagVector s (NestedVector q qs) = NestedVector <$> tag s q <*> tagVector s qs
tagVector _ _ = error "tagVector: Should not be possible"
-}