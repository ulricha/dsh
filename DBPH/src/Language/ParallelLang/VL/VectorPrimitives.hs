module Language.ParallelLang.VL.VectorPrimitives where

import qualified Language.ParallelLang.Common.Data.Type as Ty
--import qualified Language.ParallelLang.VL.Data.VectorTypes as T
import Language.ParallelLang.Common.Data.Val
import qualified Language.ParallelLang.FKL.Data.FKL as FKL
import Language.ParallelLang.Common.Data.Op

import Control.Applicative
import Language.ParallelLang.VL.Algebra
import Language.ParallelLang.VL.Data.Query

import Database.Algebra.Graph.GraphBuilder

-- FIXME this should import a module from TableAlgebra which defines 
-- common types like schema info and abstract column types.
import Database.Algebra.Pathfinder

-- * Vector primitive constructor functions

class VectorAlgebra a where
  groupBy :: Plan -> Plan -> Graph a Plan
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
  rename :: Plan -> Plan -> Graph a Plan
  propagateIn :: Plan -> Plan -> Graph a Plan
  singletonVec :: Plan -> Graph a Plan
  append :: Plan -> Plan -> Graph a Plan
  segment :: Plan -> Graph a Plan
  restrictVec :: Plan -> Plan -> Graph a Plan
  combineVec :: Plan -> Plan -> Plan -> Graph a Plan
  bPermuteVec :: Plan -> Plan -> Graph a Plan
  constructLiteral :: Ty.Type -> Val -> Graph a Plan
  tableRef :: String -> [FKL.Column Ty.Type] -> KeyInfos -> Graph a Plan
  tagVector :: String -> Plan -> Graph a Plan
  emptyVector :: SchemaInfos -> Graph a AlgNode
  binOp :: Bool -> Oper -> Plan -> Plan -> Graph a Plan
  ifPrimValues :: Plan -> Plan -> Plan -> Graph a Plan
  ifValueVectors :: Plan -> Plan -> Plan -> Graph a Plan
  initialLoop :: a

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
                    
