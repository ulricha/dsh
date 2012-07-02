{-# LANGUAGE TemplateHaskell, TypeSynonymInstances, FlexibleInstances #-}
module Language.ParallelLang.VL.VLPrimitives where
    
import Language.ParallelLang.VL.Data.DBVector
import Language.ParallelLang.VL.VectorPrimitives
import Language.ParallelLang.VL.Data.VectorLanguage as V

import Database.Algebra.Dag.Common as C
import Database.Algebra.Dag.Builder

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

instance VectorAlgebra VL where
    -- unique :: DBV -> GraphM r a DBV
    unique (DBV c _) = dbv $ insertNode $ UnOp Unique c
    -- uniqueL :: DBV -> GraphM r a DBV
    uniqueL (DBV c _) = dbv $ insertNode $ UnOp UniqueL c
    -- groupBy :: DBV -> DBV -> GraphM r a (DescrVector, DBV, PropVector)
    groupBy (DBV c1 _) (DBV c2 _) = do
                                      r <- insertNode $ C.BinOp GroupBy c1 c2
                                      r1 <- descr $ insertNode $ UnOp R1 r
                                      r2 <- dbv $ insertNode $ UnOp R2 r
                                      r3 <- prop $ insertNode $ UnOp R3 r
                                      return (r1, r2, r3) 
    -- sortWith :: DBV -> DBV -> GraphM r a (DBV, PropVector)
    sortWith (DBV c1 _) (DBV c2 _) = do
                                      r <- insertNode $ C.BinOp SortWith c1 c2
                                      r1 <- dbv $ insertNode $ UnOp R1 r
                                      r2 <- prop $ insertNode $ UnOp R2 r
                                      return (r1, r2)
    -- notPrim :: DBP -> GraphM r a DBP
    notPrim (DBP c _) = dbp $ insertNode $ UnOp NotPrim c    
    -- notVec :: DBV -> GraphM r a DBV
    notVec (DBV c _) = dbv $ insertNode $ UnOp NotVec c
    -- lengthA :: DescrVector -> GraphM r a DBP
    lengthA (DescrVector c) = dbp $ insertNode $ UnOp LengthA c
    -- lengthSeg :: DescrVector -> DescrVector -> GraphM r a DBV
    lengthSeg (DescrVector c1) (DescrVector c2) = dbv $ insertNode $ C.BinOp LengthSeg c1 c2
    -- descToRename :: DescrVector -> GraphM r a RenameVector
    descToRename (DescrVector c) = rename $ insertNode $ C.UnOp DescToRename c
    -- toDescr :: DBV -> GraphM r a DescrVector
    toDescr (DBV c _) = descr $ insertNode $ C.UnOp ToDescr c
    -- distPrim :: DBP -> DescrVector -> GraphM r a (DBV, PropVector)
    distPrim (DBP c1 _) (DescrVector c2) = do
                                            r <- insertNode $ C.BinOp DistPrim c1 c2
                                            r1 <- dbv $ insertNode $ UnOp R1 r
                                            r2 <- prop $ insertNode $ UnOp R2 r
                                            return (r1, r2)
    -- distDesc :: DBV -> DescrVector -> GraphM r a (DBV, PropVector)
    distDesc (DBV c1 _) (DescrVector c2) = do
                                            r <- insertNode $ C.BinOp DistDesc c1 c2
                                            r1 <- dbv $ insertNode $ UnOp R1 r
                                            r2 <- prop $ insertNode $ UnOp R2 r
                                            return (r1, r2)
    -- distLift :: DBV -> DescrVector -> GraphM r a (DBV, PropVector)
    distLift (DBV c1 _) (DescrVector c2) = do
                                            r <- insertNode $ C.BinOp DistLift c1 c2
                                            r1 <- dbv $ insertNode $ UnOp R1 r
                                            r2 <- prop $ insertNode $ UnOp R2 r
                                            return (r1, r2)
    -- -- | propRename uses a propagation vector to rename a vector (no filtering or reordering).
    -- propRename :: RenameVector -> DBV -> GraphM r a DBV
    propRename (RenameVector c1) (DBV c2 _) = dbv $ insertNode $ C.BinOp PropRename c1 c2
    -- -- | propFilter uses a propagation vector to rename and filter a vector (no reordering).
    -- propFilter :: RenameVector -> DBV -> GraphM r a (DBV, RenameVector)
    propFilter (RenameVector c1) (DBV c2 _) = do
                                                r <- insertNode $ C.BinOp PropFilter c1 c2
                                                r1 <- dbv $ insertNode $ UnOp R1 r
                                                r2 <- rename $ insertNode $ UnOp R2 r 
                                                return (r1, r2)
    -- -- | propReorder uses a propagation vector to rename, filter and reorder a vector.
    -- propReorder :: PropVector -> DBV -> GraphM r a (DBV, PropVector)
    propReorder (PropVector c1) (DBV c2 _) = do
                                               r <- insertNode $ C.BinOp PropReorder c1 c2
                                               r1 <- dbv $ insertNode $ UnOp R1 r
                                               r2 <- prop $ insertNode $ UnOp R2 r
                                               return (r1, r2)
    -- singletonDescr :: GraphM r a DescrVector
    singletonDescr = descr $ insertNode $ NullaryOp SingletonDescr
    -- append :: DBV -> DBV -> GraphM r a (DBV, RenameVector, RenameVector)
    append (DBV c1 _) (DBV c2 _) = do
                                    r <- insertNode $ C.BinOp Append c1 c2
                                    r1 <- dbv $ insertNode $ UnOp R1 r
                                    r2 <- rename $ insertNode $ UnOp R2 r
                                    r3 <- rename $ insertNode $ UnOp R3 r
                                    return (r1, r2, r3)
    -- segment :: DBV -> GraphM r a DBV
    segment (DBV c _) = dbv $ insertNode $ UnOp Segment c
    -- restrictVec :: DBV -> DBV -> GraphM r a (DBV, RenameVector)
    restrictVec (DBV c1 _) (DBV c2 _) = do
                                         r <- insertNode $ C.BinOp RestrictVec c1 c2
                                         r1 <- dbv $ insertNode $ UnOp R1 r
                                         r2 <- rename $ insertNode $ UnOp R2 r
                                         return (r1, r2)
    -- combineVec :: DBV -> DBV -> DBV -> GraphM r a (DBV, RenameVector, RenameVector)
    combineVec (DBV c1 _) (DBV c2 _) (DBV c3 _) = do
                                                   r <- insertNode $ TerOp CombineVec c1 c2 c3
                                                   r1 <- dbv $ insertNode $ UnOp R1 r
                                                   r2 <- rename $ insertNode $ UnOp R2 r
                                                   r3 <- rename $ insertNode $ UnOp R3 r
                                                   return (r1, r2, r3)
    -- constructLiteralValue :: [Ty.Type] -> [PVal] -> GraphM r a DBP
    constructLiteralValue tys vals = dbp $ insertNode $ NullaryOp $ ConstructLiteralValue tys vals
    -- constructLiteralTable :: [Ty.Type] -> [[PVal]] -> GraphM r a DBV
    constructLiteralTable tys vals = dbv $ insertNode $ NullaryOp $ ConstructLiteralTable tys vals
    -- tableRef :: String -> [TypedColumn] -> [Key] -> GraphM r a DBV
    tableRef n tys ks = dbv $ insertNode $ NullaryOp $ TableRef n tys ks
    -- binOp :: Oper -> DBP -> DBP -> GraphM r a DBP
    binOp o (DBP c1 _) (DBP c2 _) = dbp $ insertNode $ C.BinOp (V.BinOp o) c1 c2
    -- binOpL :: Oper -> DBV -> DBV -> GraphM r a DBV
    binOpL o (DBV c1 _) (DBV c2 _) = dbv $ insertNode $ C.BinOp (V.BinOpL o) c1 c2
    -- vecSum :: Ty.Type -> DBV -> GraphM r a DBP
    vecSum ty (DBV c _) = dbp $ insertNode $ UnOp (VecSum ty) c
    -- vecSumLift :: DescrVector -> DBV -> GraphM r a DBV
    vecSumLift (DescrVector c1) (DBV c2 _) = dbv $ insertNode $ C.BinOp VecSumL c1 c2
    -- vecMin :: DBV -> GraphM r a DBP
    vecMin (DBV c _) = dbp $ insertNode $ UnOp VecMin c
    -- vecMinLift :: DBV -> GraphM r a DBV
    vecMinLift (DBV c _) = dbv $ insertNode $ UnOp VecMinL c
    -- vecMax :: DBV -> GraphM r a DBP
    vecMax (DBV c _) = dbp $ insertNode $ UnOp VecMax c
    -- vecMaxLift :: DBV -> GraphM r a DBV 
    vecMaxLift (DBV c _) = dbv $ insertNode $ UnOp VecMaxL c
    -- selectPos :: DBV -> Oper -> DBP -> GraphM r a (DBV, RenameVector)
    selectPos (DBV c1 _) op (DBP c2 _) = do
                                            r <- insertNode $ C.BinOp (SelectPos op) c1 c2
                                            r1 <- dbv $ insertNode $ UnOp R1 r
                                            r2 <- rename $ insertNode $ UnOp R2 r
                                            return (r1, r2)
    -- selectPosLift :: DBV -> Oper -> DBV -> GraphM r a (DBV, RenameVector)
    selectPosLift (DBV c1 _) op (DBV c2 _) = do
                                              r <- insertNode $ C.BinOp (SelectPosL op) c1 c2
                                              r1 <- dbv $ insertNode $ UnOp R1 r
                                              r2 <- rename $ insertNode $ UnOp R2 r
                                              return (r1, r2)
    -- projectL :: DBV -> [DBCol] -> GraphM r a DBV
    projectL (DBV c _) cols = dbv $ insertNode $ UnOp (ProjectL cols) c
    -- projectA :: DBP -> [DBCol] -> GraphM r a DBP
    projectA (DBP c _) cols = dbp $ insertNode $ UnOp (ProjectA cols) c
    -- pairA :: DBP -> DBP -> GraphM r a DBP
    pairA (DBP c1 _) (DBP c2 _) = dbp $ insertNode $ C.BinOp PairA c1 c2
    -- pairL :: DBV -> DBV -> GraphM r a DBV
    pairL (DBV c1 _) (DBV c2 _) = dbv $ insertNode $ C.BinOp PairL c1 c2
    -- zipL :: DBV -> DBV -> GraphM r a (DBV, RenameVector, RenameVector)
    zipL (DBV c1 _) (DBV c2 _) = do
                                  r <- insertNode $ C.BinOp ZipL c1 c2
                                  r1 <- dbv $ insertNode $ UnOp R1 r
                                  r2 <- rename $ insertNode $ UnOp R2 r
                                  r3 <- rename $ insertNode $ UnOp R3 r
                                  return (r1, r2, r3)
    -- integerToDoubleA :: DBP -> GraphM r a DBP
    integerToDoubleA (DBP c _) = dbp $ insertNode $ UnOp IntegerToDoubleA c
    -- integerToDoubleL :: DBV -> GraphM r a DBV
    integerToDoubleL (DBV c _) = dbv $ insertNode $ UnOp IntegerToDoubleL c
    -- reverseA :: DBV -> GraphM r a (DBV, PropVector)
    reverseA (DBV c _) = do
                          r <- insertNode $ UnOp ReverseA c
                          r1 <- dbv $ insertNode $ UnOp R1 r
                          r2 <- prop $ insertNode $ UnOp R2 r
                          return (r1, r2)
    -- reverseL :: DBV -> GraphM r a (DBV, PropVector)
    reverseL (DBV c _) = do
                           r <- insertNode $ UnOp ReverseL c
                           r1 <- dbv $ insertNode $ UnOp R1 r
                           r2 <- prop $ insertNode $ UnOp R2 r
                           return (r1, r2)
    -- falsePositions :: DBV -> GraphM r a DBV
    falsePositions (DBV c _) = dbv $ insertNode $ UnOp FalsePositions c
                                
