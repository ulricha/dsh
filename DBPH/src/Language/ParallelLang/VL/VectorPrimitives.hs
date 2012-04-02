module Language.ParallelLang.VL.VectorPrimitives where

import qualified Language.ParallelLang.Common.Data.Type as Ty
--import qualified Language.ParallelLang.VL.Data.VectorTypes as T
import Language.ParallelLang.Common.Data.Val
import Language.ParallelLang.FKL.Data.FKL
import Language.ParallelLang.Common.Data.Op

import Control.Applicative
import Language.ParallelLang.VL.Algebra
import Language.ParallelLang.VL.Data.Query

import Database.Algebra.Dag.Builder

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
  groupBy :: Plan -> Plan -> Graph a (Plan, Plan, PropVector)
  sortWith :: Plan -> Plan -> Graph a (Plan, PropVector)
  notPrim :: Plan -> Graph a Plan
  notVec :: Plan -> Graph a Plan
  lengthA :: Plan -> Graph a Plan
  lengthSeg :: Plan -> Plan -> Graph a Plan
  descToRename :: Plan -> Graph a RenameVector
  notA :: Plan -> Graph a Plan
  outer :: Plan -> Graph a Plan
  distPrim :: Plan -> Plan -> Graph a Plan
  distDesc :: Plan -> Plan -> Graph a (Plan, RenameVector)
  distLift :: Plan -> Plan -> Graph a (Plan, RenameVector)
  -- | propRename uses a propagation vector to rename a vector (no filtering or reordering).
  propRename :: RenameVector -> Plan -> Graph a Plan
  -- | propFilter uses a propagation vector to rename and filter a vector (no reordering).
  propFilter :: RenameVector -> Plan -> Graph a (Plan, RenameVector)
  -- | propReorder uses a propagation vector to rename, filter and reorder a vector.
  propReorder :: PropVector -> Plan -> Graph a (Plan, PropVector)
  singletonVec :: Plan -> Graph a Plan
  append :: Plan -> Plan -> Graph a (Plan, RenameVector, RenameVector)
  segment :: Plan -> Graph a Plan
  restrictVec :: Plan -> Plan -> Graph a (Plan, RenameVector)
  combineVec :: Plan -> Plan -> Plan -> Graph a (Plan, RenameVector, RenameVector)
  bPermuteVec :: Plan -> Plan -> Graph a (Plan, PropVector)
  constructLiteral :: Ty.Type -> Val -> Graph a Plan
  tableRef :: String -> [TypedColumn] -> [Key] -> Graph a Plan
  emptyVector :: Maybe Ty.Type -> Graph a Plan
  binOp :: Bool -> Oper -> Plan -> Plan -> Graph a Plan
  ifPrimList :: Plan -> Plan -> Plan -> Graph a Plan
  vecSum :: Ty.Type -> Plan -> Graph a Plan
  vecSumLift :: Plan -> Plan -> Graph a Plan
  empty :: Plan -> Graph a Plan
  emptyLift :: Plan -> Plan -> Graph a Plan
  selectPos :: Plan -> Oper -> Plan -> Graph a (Plan, RenameVector)
  selectPosLift :: Plan -> Oper -> Plan -> Graph a (Plan, RenameVector)
  fstA :: Plan -> Graph a Plan
  fstA (PairVector e1 _) = return e1
  fstA _                     = error "fstA: not a tuple"
  sndA :: Plan -> Graph a Plan
  sndA (PairVector _ e2) = return e2
  sndA _                     = error "sndA: not a tuple"
  fstL :: Plan -> Graph a Plan
  fstL (PairVector e1 _) = return e1
  fstL _                     = error "fstL: not a tuple"
  sndL :: Plan -> Graph a Plan 
  sndL (PairVector _ e2) = return e2
  sndL _                     = error "sndL: not a tuple"

-- some purely compile time functions which involve no algebra code generation and 
-- are therefore the same for all instances of VectorAlgebra

concatV :: Plan -> Graph a Plan
concatV (NestedVector _ p) = return p
concatV (PairVector e1 e2) = PairVector <$> concatV e1 <*> concatV e2
concatV (AClosure n v l fvs x f1 f2) | l > 1 = AClosure n <$> (concatV v) 
                                                             <*> pure (l - 1) 
                                                             <*> (mapM (\(y, val) -> do
                                                                                        val' <- concatV val
                                                                                        return (y, val')) fvs)
                                                             <*> pure x <*> pure f1 <*> pure f2
concatV e                  = error $ "Not supported by concatV: " ++ show e

-- move a descriptor from e1 to e2
unconcatV :: Plan -> Plan -> Graph a Plan
unconcatV (PairVector e1 _) q = unconcatV e1 q
unconcatV (NestedVector d _) q = return $ NestedVector d q
unconcatV e1 e2                = error $ "unconcatV: Not supported: " ++ show e1 ++ " " ++ show e2

isValueVector :: Plan -> Bool
isValueVector (ValueVector _) = True
isValueVector _               = False

attachV :: Plan -> Plan -> Plan
attachV (DescrVector q1) e2 = NestedVector q1 e2
attachV _ _ = error "attachVPF: Should not be possible"
                
singletonPrim :: VectorAlgebra a => Plan -> Graph a Plan
singletonPrim (PrimVal q1) = do
                    return $ ValueVector q1
singletonPrim _ = error "singletonPrim: Should not be possible"
                    
tagVector :: String -> Plan -> Graph a Plan
tagVector s (PairVector e1 e2) = PairVector <$> tagVector s e1 <*> tagVector s e2
tagVector s (DescrVector q) = DescrVector <$> tag s q
tagVector s (ValueVector q) = ValueVector <$> tag s q
tagVector s (PrimVal q) = PrimVal <$> tag s q
tagVector s (NestedVector q qs) = NestedVector <$> tag s q <*> tagVector s qs
tagVector _ _ = error "tagVector: Should not be possible"
