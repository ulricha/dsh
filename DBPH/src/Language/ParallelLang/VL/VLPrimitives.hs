{-# LANGUAGE TemplateHaskell, TypeSynonymInstances, FlexibleInstances #-}
module Language.ParallelLang.VL.VLPrimitives where
    
import Language.ParallelLang.VL.Data.DBVector
-- import Language.ParallelLang.VL.VectorPrimitives
import qualified Language.ParallelLang.Common.Data.Type as Ty
import qualified Language.ParallelLang.Common.Data.Op as O

import Database.Algebra.Dag.Common
import Database.Algebra.Dag.Builder
import Database.Algebra.VL.Data hiding (DBCol)
import qualified Database.Algebra.VL.Data as D

dbv :: GraphM r a AlgNode -> GraphM r a DBV
dbv = fmap (flip DBV [])

dbp :: GraphM r a AlgNode -> GraphM r a DBP
dbp = fmap (flip DBP [])
         
descr :: GraphM r a AlgNode -> GraphM r a DescrVector
descr = fmap DescrVector

prop :: GraphM r a AlgNode -> GraphM r a PropVector
prop = fmap PropVector

rename :: GraphM r a AlgNode -> GraphM r a RenameVector
rename = fmap RenameVector

emptyVL :: VL
emptyVL = NullaryOp $ TableRef "Null" [] []
          
mapSnd :: (b -> c) -> (a, b) -> (a, c)
mapSnd f (a, b) = (a, f b)

typeToVLType :: Ty.Type -> VLType
typeToVLType t = case t of
  Ty.Nat -> D.Nat
  Ty.Int -> D.Int
  Ty.Bool -> D.Bool
  Ty.String -> D.String
  Ty.Unit -> D.Unit
  Ty.Double -> D.Double
  Ty.Pair t1 t2 -> D.Pair (typeToVLType t1) (typeToVLType t2)
  Ty.List t' -> D.VLList (typeToVLType t')
  Ty.Fn _ _ -> error "VLPrimitives: Functions can not occur in operator plans"
  Ty.Var _ -> error "VLPrimitives: Variables can not occur in operator plans"
  
operToVecOp :: O.Oper -> D.VecOp
operToVecOp op = case op of
  O.Add -> D.Add
  O.Sub  -> D.Sub 
  O.Div  -> D.Div 
  O.Mul  -> D.Mul 
  O.Mod  -> D.Mod 
  O.Eq   -> D.Eq  
  O.Gt   -> D.Gt  
  O.GtE  -> D.GtE 
  O.Lt   -> D.Lt  
  O.LtE  -> D.LtE 
  O.Cons  -> D.Cons 
  O.Conj  -> D.Conj 
  O.Disj  -> D.Disj 
  
unique :: DBV -> GraphM r VL DBV
unique (DBV c _) = dbv $ insertNode $ UnOp Unique c

uniqueL :: DBV -> GraphM r VL DBV
uniqueL (DBV c _) = dbv $ insertNode $ UnOp UniqueL c

groupBy :: DBV -> DBV -> GraphM r VL (DescrVector, DBV, PropVector)
groupBy (DBV c1 _) (DBV c2 _) = do
                                  r <- insertNode $ BinOp GroupBy c1 c2
                                  r1 <- descr $ insertNode $ UnOp R1 r
                                  r2 <- dbv $ insertNode $ UnOp R2 r
                                  r3 <- prop $ insertNode $ UnOp R3 r
                                  return (r1, r2, r3) 

sortWith :: DBV -> DBV -> GraphM r VL (DBV, PropVector)
sortWith (DBV c1 _) (DBV c2 _) = do
                                  r <- insertNode $ BinOp SortWith c1 c2
                                  r1 <- dbv $ insertNode $ UnOp R1 r
                                  r2 <- prop $ insertNode $ UnOp R2 r
                                  return (r1, r2)

notPrim :: DBP -> GraphM r VL DBP
notPrim (DBP c _) = dbp $ insertNode $ UnOp NotPrim c    

notVec :: DBV -> GraphM r VL DBV
notVec (DBV c _) = dbv $ insertNode $ UnOp NotVec c

lengthA :: DescrVector -> GraphM r VL DBP
lengthA (DescrVector c) = dbp $ insertNode $ UnOp LengthA c

lengthSeg :: DescrVector -> DescrVector -> GraphM r VL DBV
lengthSeg (DescrVector c1) (DescrVector c2) = dbv $ insertNode $ BinOp LengthSeg c1 c2

descToRename :: DescrVector -> GraphM r VL RenameVector
descToRename (DescrVector c) = rename $ insertNode $ UnOp DescToRename c

toDescr :: DBV -> GraphM r VL DescrVector
toDescr (DBV c _) = descr $ insertNode $ UnOp ToDescr c

distPrim :: DBP -> DescrVector -> GraphM r VL (DBV, PropVector)
distPrim (DBP c1 _) (DescrVector c2) = do
                                        r <- insertNode $ BinOp DistPrim c1 c2
                                        r1 <- dbv $ insertNode $ UnOp R1 r
                                        r2 <- prop $ insertNode $ UnOp R2 r
                                        return (r1, r2)

distDesc :: DBV -> DescrVector -> GraphM r VL (DBV, PropVector)
distDesc (DBV c1 _) (DescrVector c2) = do
                                        r <- insertNode $ BinOp DistDesc c1 c2
                                        r1 <- dbv $ insertNode $ UnOp R1 r
                                        r2 <- prop $ insertNode $ UnOp R2 r
                                        return (r1, r2)

distLift :: DBV -> DescrVector -> GraphM r VL (DBV, PropVector)
distLift (DBV c1 _) (DescrVector c2) = do
                                        r <- insertNode $ BinOp DistLift c1 c2
                                        r1 <- dbv $ insertNode $ UnOp R1 r
                                        r2 <- prop $ insertNode $ UnOp R2 r
                                        return (r1, r2)

-- | propRename uses a propagation vector to rename a vector (no filtering or reordering).
propRename :: RenameVector -> DBV -> GraphM r VL DBV
propRename (RenameVector c1) (DBV c2 _) = dbv $ insertNode $ BinOp PropRename c1 c2

-- | propFilter uses a propagation vector to rename and filter a vector (no reordering).
propFilter :: RenameVector -> DBV -> GraphM r VL (DBV, RenameVector)
propFilter (RenameVector c1) (DBV c2 _) = do
                                            r <- insertNode $ BinOp PropFilter c1 c2
                                            r1 <- dbv $ insertNode $ UnOp R1 r
                                            r2 <- rename $ insertNode $ UnOp R2 r 
                                            return (r1, r2)

-- | propReorder uses a propagation vector to rename, filter and reorder a vector.
propReorder :: PropVector -> DBV -> GraphM r VL (DBV, PropVector)
propReorder (PropVector c1) (DBV c2 _) = do
                                           r <- insertNode $ BinOp PropReorder c1 c2
                                           r1 <- dbv $ insertNode $ UnOp R1 r
                                           r2 <- prop $ insertNode $ UnOp R2 r
                                           return (r1, r2)

singletonDescr :: GraphM r VL DescrVector
singletonDescr = descr $ insertNode $ NullaryOp SingletonDescr

append :: DBV -> DBV -> GraphM r VL (DBV, RenameVector, RenameVector)
append (DBV c1 _) (DBV c2 _) = do
                                r <- insertNode $ BinOp Append c1 c2
                                r1 <- dbv $ insertNode $ UnOp R1 r
                                r2 <- rename $ insertNode $ UnOp R2 r
                                r3 <- rename $ insertNode $ UnOp R3 r
                                return (r1, r2, r3)

segment :: DBV -> GraphM r VL DBV
segment (DBV c _) = dbv $ insertNode $ UnOp Segment c

restrictVec :: DBV -> DBV -> GraphM r VL (DBV, RenameVector)
restrictVec (DBV c1 _) (DBV c2 _) = do
                                     r <- insertNode $ BinOp RestrictVec c1 c2
                                     r1 <- dbv $ insertNode $ UnOp R1 r
                                     r2 <- rename $ insertNode $ UnOp R2 r
                                     return (r1, r2)

combineVec :: DBV -> DBV -> DBV -> GraphM r VL (DBV, RenameVector, RenameVector)
combineVec (DBV c1 _) (DBV c2 _) (DBV c3 _) = do
                                               r <- insertNode $ TerOp CombineVec c1 c2 c3
                                               r1 <- dbv $ insertNode $ UnOp R1 r
                                               r2 <- rename $ insertNode $ UnOp R2 r
                                               r3 <- rename $ insertNode $ UnOp R3 r
                                               return (r1, r2, r3)

constructLiteralValue :: [Ty.Type] -> [VLVal] -> GraphM r VL DBP
constructLiteralValue tys vals = dbp $ insertNode $ NullaryOp $ ConstructLiteralValue (map typeToVLType tys) vals

constructLiteralTable :: [Ty.Type] -> [[VLVal]] -> GraphM r VL DBV
constructLiteralTable tys vals = dbv $ insertNode $ NullaryOp $ ConstructLiteralTable (map typeToVLType tys) vals

tableRef :: String -> [TypedColumn] -> [Key] -> GraphM r VL DBV
tableRef n tys ks = dbv $ insertNode $ NullaryOp $ TableRef n ({-map (mapSnd typeToVLType)-} tys) ks

binOp :: O.Oper -> DBP -> DBP -> GraphM r VL DBP
binOp o (DBP c1 _) (DBP c2 _) = dbp $ insertNode $ BinOp (VecBinOp (operToVecOp o)) c1 c2

binOpL :: O.Oper -> DBV -> DBV -> GraphM r VL DBV
binOpL o (DBV c1 _) (DBV c2 _) = dbv $ insertNode $ BinOp (VecBinOpL (operToVecOp o)) c1 c2

vecSum :: Ty.Type -> DBV -> GraphM r VL DBP
vecSum ty (DBV c _) = dbp $ insertNode $ UnOp (VecSum (typeToVLType ty)) c

vecSumLift :: DescrVector -> DBV -> GraphM r VL DBV
vecSumLift (DescrVector c1) (DBV c2 _) = dbv $ insertNode $ BinOp VecSumL c1 c2

vecMin :: DBV -> GraphM r VL DBP
vecMin (DBV c _) = dbp $ insertNode $ UnOp VecMin c

vecMinLift :: DBV -> GraphM r VL DBV
vecMinLift (DBV c _) = dbv $ insertNode $ UnOp VecMinL c

vecMax :: DBV -> GraphM r VL DBP
vecMax (DBV c _) = dbp $ insertNode $ UnOp VecMax c

vecMaxLift :: DBV -> GraphM r VL DBV 
vecMaxLift (DBV c _) = dbv $ insertNode $ UnOp VecMaxL c

selectPos :: DBV -> O.Oper -> DBP -> GraphM r VL (DBV, RenameVector)
selectPos (DBV c1 _) op (DBP c2 _) = do
                                        r <- insertNode $ BinOp (SelectPos (operToVecOp op)) c1 c2
                                        r1 <- dbv $ insertNode $ UnOp R1 r
                                        r2 <- rename $ insertNode $ UnOp R2 r
                                        return (r1, r2)

selectPosLift :: DBV -> O.Oper -> DBV -> GraphM r VL (DBV, RenameVector)
selectPosLift (DBV c1 _) op (DBV c2 _) = do
                                          r <- insertNode $ BinOp (SelectPosL (operToVecOp op)) c1 c2
                                          r1 <- dbv $ insertNode $ UnOp R1 r
                                          r2 <- rename $ insertNode $ UnOp R2 r
                                          return (r1, r2)

projectL :: DBV -> [DBCol] -> GraphM r VL DBV
projectL (DBV c _) cols = dbv $ insertNode $ UnOp (ProjectL cols) c

projectA :: DBP -> [DBCol] -> GraphM r VL DBP
projectA (DBP c _) cols = dbp $ insertNode $ UnOp (ProjectA cols) c

pairA :: DBP -> DBP -> GraphM r VL DBP
pairA (DBP c1 _) (DBP c2 _) = dbp $ insertNode $ BinOp PairA c1 c2

pairL :: DBV -> DBV -> GraphM r VL DBV
pairL (DBV c1 _) (DBV c2 _) = dbv $ insertNode $ BinOp PairL c1 c2

zipL :: DBV -> DBV -> GraphM r VL (DBV, RenameVector, RenameVector)
zipL (DBV c1 _) (DBV c2 _) = do
                              r <- insertNode $ BinOp ZipL c1 c2
                              r1 <- dbv $ insertNode $ UnOp R1 r
                              r2 <- rename $ insertNode $ UnOp R2 r
                              r3 <- rename $ insertNode $ UnOp R3 r
                              return (r1, r2, r3)

integerToDoubleA :: DBP -> GraphM r VL DBP
integerToDoubleA (DBP c _) = dbp $ insertNode $ UnOp IntegerToDoubleA c

integerToDoubleL :: DBV -> GraphM r VL DBV
integerToDoubleL (DBV c _) = dbv $ insertNode $ UnOp IntegerToDoubleL c

reverseA :: DBV -> GraphM r VL (DBV, PropVector)
reverseA (DBV c _) = do
                      r <- insertNode $ UnOp ReverseA c
                      r1 <- dbv $ insertNode $ UnOp R1 r
                      r2 <- prop $ insertNode $ UnOp R2 r
                      return (r1, r2)

reverseL :: DBV -> GraphM r VL (DBV, PropVector)
reverseL (DBV c _) = do
                       r <- insertNode $ UnOp ReverseL c
                       r1 <- dbv $ insertNode $ UnOp R1 r
                       r2 <- prop $ insertNode $ UnOp R2 r
                       return (r1, r2)

falsePositions :: DBV -> GraphM r VL DBV
falsePositions (DBV c _) = dbv $ insertNode $ UnOp FalsePositions c
                                
