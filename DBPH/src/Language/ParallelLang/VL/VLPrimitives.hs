{-# LANGUAGE TemplateHaskell, TypeSynonymInstances, FlexibleInstances #-}
module Language.ParallelLang.VL.VLPrimitives where
    
import Language.ParallelLang.VL.Data.DBVector
import Language.ParallelLang.VL.VectorPrimitives
import qualified Language.ParallelLang.Common.Data.Type as T
import qualified Language.ParallelLang.Common.Data.Op as O

import Database.Algebra.Dag.Common
import Database.Algebra.Dag.Builder
import Database.Algebra.VL.Data
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

typeToVLType :: T.Type -> VLType
typeToVLType t = case t of
  T.Nat -> D.Nat
  T.Int -> D.Int
  T.Bool -> D.Bool
  T.String -> D.String
  T.Unit -> D.Unit
  T.Double -> D.Double
  T.Pair t1 t2 -> D.Pair (typeToVLType t1) (typeToVLType t2)
  T.List t' -> D.VLList (typeToVLType t')
  T.Fn _ _ -> error "VLPrimitives: Functions can not occur in operator plans"
  T.Var _ -> error "VLPrimitives: Variables can not occur in operator plans"
  
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
  
pValToVLVal :: PVal -> VLVal
pValToVLVal v = case v of 
  PInt i -> VLInt i
  PNat i -> VLNat i
  PBool b -> VLBool b
  PString s -> VLString s
  PDouble d -> VLDouble d
  PUnit -> VLUnit

instance VectorAlgebra VL where
    -- unique :: DBV -> GraphM r a DBV
    unique (DBV c _) = dbv $ insertNode $ UnOp Unique c
    -- uniqueL :: DBV -> GraphM r a DBV
    uniqueL (DBV c _) = dbv $ insertNode $ UnOp UniqueL c
    -- groupBy :: DBV -> DBV -> GraphM r a (DescrVector, DBV, PropVector)
    groupBy (DBV c1 _) (DBV c2 _) = do
                                      r <- insertNode $ BinOp GroupBy c1 c2
                                      r1 <- descr $ insertNode $ UnOp R1 r
                                      r2 <- dbv $ insertNode $ UnOp R2 r
                                      r3 <- prop $ insertNode $ UnOp R3 r
                                      return (r1, r2, r3) 
    -- sortWith :: DBV -> DBV -> GraphM r a (DBV, PropVector)
    sortWith (DBV c1 _) (DBV c2 _) = do
                                      r <- insertNode $ BinOp SortWith c1 c2
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
    lengthSeg (DescrVector c1) (DescrVector c2) = dbv $ insertNode $ BinOp LengthSeg c1 c2
    -- descToRename :: DescrVector -> GraphM r a RenameVector
    descToRename (DescrVector c) = rename $ insertNode $ UnOp DescToRename c
    -- toDescr :: DBV -> GraphM r a DescrVector
    toDescr (DBV c _) = descr $ insertNode $ UnOp ToDescr c
    -- distPrim :: DBP -> DescrVector -> GraphM r a (DBV, PropVector)
    distPrim (DBP c1 _) (DescrVector c2) = do
                                            r <- insertNode $ BinOp DistPrim c1 c2
                                            r1 <- dbv $ insertNode $ UnOp R1 r
                                            r2 <- prop $ insertNode $ UnOp R2 r
                                            return (r1, r2)
    -- distDesc :: DBV -> DescrVector -> GraphM r a (DBV, PropVector)
    distDesc (DBV c1 _) (DescrVector c2) = do
                                            r <- insertNode $ BinOp DistDesc c1 c2
                                            r1 <- dbv $ insertNode $ UnOp R1 r
                                            r2 <- prop $ insertNode $ UnOp R2 r
                                            return (r1, r2)
    -- distLift :: DBV -> DescrVector -> GraphM r a (DBV, PropVector)
    distLift (DBV c1 _) (DescrVector c2) = do
                                            r <- insertNode $ BinOp DistLift c1 c2
                                            r1 <- dbv $ insertNode $ UnOp R1 r
                                            r2 <- prop $ insertNode $ UnOp R2 r
                                            return (r1, r2)
    -- -- | propRename uses a propagation vector to rename a vector (no filtering or reordering).
    -- propRename :: RenameVector -> DBV -> GraphM r a DBV
    propRename (RenameVector c1) (DBV c2 _) = dbv $ insertNode $ BinOp PropRename c1 c2
    -- -- | propFilter uses a propagation vector to rename and filter a vector (no reordering).
    -- propFilter :: RenameVector -> DBV -> GraphM r a (DBV, RenameVector)
    propFilter (RenameVector c1) (DBV c2 _) = do
                                                r <- insertNode $ BinOp PropFilter c1 c2
                                                r1 <- dbv $ insertNode $ UnOp R1 r
                                                r2 <- rename $ insertNode $ UnOp R2 r 
                                                return (r1, r2)
    -- -- | propReorder uses a propagation vector to rename, filter and reorder a vector.
    -- propReorder :: PropVector -> DBV -> GraphM r a (DBV, PropVector)
    propReorder (PropVector c1) (DBV c2 _) = do
                                               r <- insertNode $ BinOp PropReorder c1 c2
                                               r1 <- dbv $ insertNode $ UnOp R1 r
                                               r2 <- prop $ insertNode $ UnOp R2 r
                                               return (r1, r2)
    -- singletonDescr :: GraphM r a DescrVector
    singletonDescr = descr $ insertNode $ NullaryOp SingletonDescr
    -- append :: DBV -> DBV -> GraphM r a (DBV, RenameVector, RenameVector)
    append (DBV c1 _) (DBV c2 _) = do
                                    r <- insertNode $ BinOp Append c1 c2
                                    r1 <- dbv $ insertNode $ UnOp R1 r
                                    r2 <- rename $ insertNode $ UnOp R2 r
                                    r3 <- rename $ insertNode $ UnOp R3 r
                                    return (r1, r2, r3)
    -- segment :: DBV -> GraphM r a DBV
    segment (DBV c _) = dbv $ insertNode $ UnOp Segment c
    -- restrictVec :: DBV -> DBV -> GraphM r a (DBV, RenameVector)
    restrictVec (DBV c1 _) (DBV c2 _) = do
                                         r <- insertNode $ BinOp RestrictVec c1 c2
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
    constructLiteralValue tys vals = dbp $ insertNode $ NullaryOp $ ConstructLiteralValue (map typeToVLType tys) (map pValToVLVal vals)
    -- constructLiteralTable :: [Ty.Type] -> [[PVal]] -> GraphM r a DBV
    constructLiteralTable tys vals = dbv $ insertNode $ NullaryOp $ ConstructLiteralTable (map typeToVLType tys) (map (map pValToVLVal) vals)
    -- tableRef :: String -> [TypedColumn] -> [Key] -> GraphM r a DBV
    tableRef n tys ks = dbv $ insertNode $ NullaryOp $ TableRef n (map (mapSnd typeToVLType) tys) ks
    -- binOp :: Oper -> DBP -> DBP -> GraphM r a DBP
    binOp o (DBP c1 _) (DBP c2 _) = dbp $ insertNode $ BinOp (VecBinOp (operToVecOp o)) c1 c2
    -- binOpL :: Oper -> DBV -> DBV -> GraphM r a DBV
    binOpL o (DBV c1 _) (DBV c2 _) = dbv $ insertNode $ BinOp (VecBinOpL (operToVecOp o)) c1 c2
    -- vecSum :: Ty.Type -> DBV -> GraphM r a DBP
    vecSum ty (DBV c _) = dbp $ insertNode $ UnOp (VecSum (typeToVLType ty)) c
    -- vecSumLift :: DescrVector -> DBV -> GraphM r a DBV
    vecSumLift (DescrVector c1) (DBV c2 _) = dbv $ insertNode $ BinOp VecSumL c1 c2
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
                                            r <- insertNode $ BinOp (SelectPos (operToVecOp op)) c1 c2
                                            r1 <- dbv $ insertNode $ UnOp R1 r
                                            r2 <- rename $ insertNode $ UnOp R2 r
                                            return (r1, r2)
    -- selectPosLift :: DBV -> Oper -> DBV -> GraphM r a (DBV, RenameVector)
    selectPosLift (DBV c1 _) op (DBV c2 _) = do
                                              r <- insertNode $ BinOp (SelectPosL (operToVecOp op)) c1 c2
                                              r1 <- dbv $ insertNode $ UnOp R1 r
                                              r2 <- rename $ insertNode $ UnOp R2 r
                                              return (r1, r2)
    -- projectL :: DBV -> [DBCol] -> GraphM r a DBV
    projectL (DBV c _) cols = dbv $ insertNode $ UnOp (ProjectL cols) c
    -- projectA :: DBP -> [DBCol] -> GraphM r a DBP
    projectA (DBP c _) cols = dbp $ insertNode $ UnOp (ProjectA cols) c
    -- pairA :: DBP -> DBP -> GraphM r a DBP
    pairA (DBP c1 _) (DBP c2 _) = dbp $ insertNode $ BinOp PairA c1 c2
    -- pairL :: DBV -> DBV -> GraphM r a DBV
    pairL (DBV c1 _) (DBV c2 _) = dbv $ insertNode $ BinOp PairL c1 c2
    -- zipL :: DBV -> DBV -> GraphM r a (DBV, RenameVector, RenameVector)
    zipL (DBV c1 _) (DBV c2 _) = do
                                  r <- insertNode $ BinOp ZipL c1 c2
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
                                
