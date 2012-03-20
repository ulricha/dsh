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
import Database.Algebra.Dag.Common

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
  groupBy :: Plan -> Plan -> Graph a Plan
  sortWith :: Plan -> Plan -> Graph a Plan
  notPrim :: Plan -> Graph a Plan
  notVec :: Plan -> Graph a Plan
  lengthA :: Plan -> Graph a Plan
  lengthSeg :: Plan -> Plan -> Graph a Plan
  descToProp :: Plan -> Graph a Plan
  notA :: Plan -> Graph a Plan
  outer :: Plan -> Graph a Plan
  distPrim :: Plan -> Plan -> Graph a Plan
  distDesc :: Plan -> Plan -> Graph a Plan
  distLift :: Plan -> Plan -> Graph a Plan
  -- | propRename uses a propagation vector to rename a vector (no filtering or reordering).
  propRename :: Plan -> Plan -> Graph a Plan
  -- | propFilter uses a propagation vector to rename and filter a vector (no reordering).
  propFilter :: Plan -> Plan -> Graph a Plan
  -- | propReorder uses a propagation vector to rename, filter and reorder a vector.
  propReorder :: Plan -> Plan -> Graph a Plan
  singletonVec :: Plan -> Graph a Plan
  append :: Plan -> Plan -> Graph a Plan
  segment :: Plan -> Graph a Plan
  restrictVec :: Plan -> Plan -> Graph a Plan
  combineVec :: Plan -> Plan -> Plan -> Graph a Plan
  bPermuteVec :: Plan -> Plan -> Graph a Plan
  constructLiteral :: Ty.Type -> Val -> Graph a Plan
  tableRef :: String -> [TypedColumn Ty.Type] -> [Key] -> Graph a Plan
  emptyVector :: Maybe Ty.Type -> Graph a Plan
  binOp :: Bool -> Oper -> Plan -> Plan -> Graph a Plan
  ifPrimList :: Plan -> Plan -> Plan -> Graph a Plan
  vecSum :: Ty.Type -> Plan -> Graph a Plan
  vecSumLift :: Plan -> Plan -> Graph a Plan
  empty :: Plan -> Graph a Plan
  emptyLift :: Plan -> Plan -> Graph a Plan
  selectPos :: Plan -> Oper -> Plan -> Graph a Plan
  selectPosLift :: Plan -> Oper -> Plan -> Graph a Plan
  fstA :: Plan -> Graph a Plan
  fstA (TupleVector [e1, _]) = return e1
  fstA _                     = error "fstA: not a tuple"
  sndA :: Plan -> Graph a Plan
  sndA (TupleVector [_, e2]) = return e2
  sndA _                     = error "sndA: not a tuple"
  fstL :: Plan -> Graph a Plan
  fstL (TupleVector [e1, _]) = return e1
  fstL _                     = error "fstL: not a tuple"
  sndL :: Plan -> Graph a Plan 
  sndL (TupleVector [_, e2]) = return e2
  sndL _                     = error "sndL: not a tuple"

-- some purely compile time functions which involve no algebra code generation and 
-- are therefore the same for all instances of VectorAlgebra

extract :: Plan -> Int -> Graph a Plan
extract p 0 = return p
extract (NestedVector _ p') n | n > 0 = extract p' (n - 1)
extract (AClosure n v l fvs x f1 f2) i | i < l = AClosure n <$> (extract v i) 
                                                             <*> pure (l - i) 
                                                             <*> (mapM (\(y, val) -> do
                                                                                        val' <- extract val i
                                                                                        return (y, val')) fvs)
                                                             <*> pure x <*> pure f1 <*> pure f2
extract (TupleVector es) i = TupleVector <$> mapM (flip extract i) es
extract v i = error $ "Extract: " ++ show v ++ " " ++ show i

insert :: VectorAlgebra a => Plan -> Plan -> Int -> Graph a Plan
insert p _ 0 = return p
insert p d n | n > 0 = do
                        o <- outer d
                        d' <- extract d 1
                        insert (attachV o p) d' (n - 1)
             | otherwise = error "Can't insert a negative amount of descriptors"

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
tagVector s (TupleVector vs) = TupleVector <$> (sequence $ map (\v -> tagVector s v) vs)
tagVector s (DescrVector q) = DescrVector <$> tag s q
tagVector s (ValueVector q) = ValueVector <$> tag s q
tagVector s (PrimVal q) = PrimVal <$> tag s q
tagVector s (NestedVector q qs) = NestedVector <$> tag s q <*> tagVector s qs
tagVector s (PropVector q) = PropVector <$> tag s q
tagVector _ _ = error "tagVector: Should not be possible"


{-
determineResultVector :: Plan -> Graph a (AlgNode -> Plan, AlgNode, AbstractProjInfo -> AbstractProjInfo)
determineResultVector e = do
                             let hasI = isValueVector e
                             let rf = if hasI then ValueVector else DescrVector
                             let pf = if hasI then \x -> (AuxCol Item1, AuxCol Item1):x else \x -> x
                             let q = if hasI
                                         then let (ValueVector q') = e in q'
                                         else let (DescrVector q') = e in q'
                             return (rf, q, pf)

determineResultVector' :: Plan -> Plan -> Graph a (AlgNode -> Plan, AlgNode, AlgNode, AbstractProjInfo -> AbstractProjInfo)
determineResultVector' e1 e2 = do
                                 let hasI = isValueVector e1
                                 let rf = if hasI then ValueVector else DescrVector
                                 let pf = if hasI then \x -> (AuxCol Item1, AuxCol Item1):x else \x -> x
                                 let (q1, q2) = if hasI
                                                 then let (ValueVector q1') = e1
                                                          (ValueVector q2') = e2 in (q1', q2')
                                                 else let (DescrVector q1') = e1 
                                                          (DescrVector q2') = e2 in (q1', q2')
                                 return (rf, q1, q2, pf)

-}
