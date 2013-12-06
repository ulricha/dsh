-- FIXME should be able to combine most of the functions        

{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Database.DSH.VL.VLPrimitives where

import qualified Database.DSH.Common.Data.Op   as O
import qualified Database.DSH.Common.Data.Type as Ty
import qualified Database.DSH.Common.Data.Val as V
import           Database.DSH.Common.Data.JoinExpr
import           Database.DSH.VL.Data.DBVector

import           Database.DSH.Impossible

import           Database.Algebra.Dag.Builder
import           Database.Algebra.Dag.Common
import           Database.Algebra.VL.Data                 hiding (DBCol)
import qualified Database.Algebra.VL.Data                 as D

dbv :: GraphM r a AlgNode -> GraphM r a DBV
dbv = fmap (flip DBV [])

dbp :: GraphM r a AlgNode -> GraphM r a DBP
dbp = fmap (flip DBP [])

prop :: GraphM r a AlgNode -> GraphM r a PropVector
prop = fmap PropVector

rename :: GraphM r a AlgNode -> GraphM r a RenameVector
rename = fmap RenameVector

emptyVL :: VL
emptyVL = NullaryOp $ TableRef "Null" [] []

mapSnd :: (b -> c) -> (a, b) -> (a, c)
mapSnd f (a, b) = (a, f b)

pVal :: V.Val -> VLVal
pVal (V.IntV i)    = VLInt i
pVal (V.BoolV b)   = VLBool b
pVal (V.StringV s) = VLString s
pVal (V.DoubleV d) = VLDouble d
pVal V.UnitV       = VLUnit
pVal _             = error "pVal: Not a supported value"

typeToVLType :: Ty.Type -> VLType
typeToVLType t = case t of
  Ty.NatT        -> D.Nat
  Ty.IntT        -> D.Int
  Ty.BoolT       -> D.Bool
  Ty.StringT     -> D.String
  Ty.UnitT       -> D.Unit
  Ty.DoubleT     -> D.Double
  Ty.PairT t1 t2 -> D.Pair (typeToVLType t1) (typeToVLType t2)
  Ty.ListT t'    -> D.VLList (typeToVLType t')
  Ty.FunT _ _    -> error "VLPrimitives: Functions can not occur in operator plans"
  Ty.VarT _      -> error "VLPrimitives: Variables can not occur in operator plans"

operToVecOp :: O.Oper -> D.VecOp
operToVecOp op = case op of
  O.Add  -> D.NOp D.Add
  O.Sub  -> D.NOp D.Sub
  O.Div  -> D.NOp D.Div
  O.Mul  -> D.NOp D.Mul
  O.Mod  -> D.NOp D.Mod
  O.Cons -> $impossible
  O.Conj -> D.BOp D.Conj
  O.Disj -> D.BOp D.Disj
  O.Like -> D.Like
  _      -> D.COp $ operToCompOp op

joinExpr :: JoinExpr -> Expr1
joinExpr expr = aux 1 expr
  where
    aux :: Int -> JoinExpr -> Expr1
    aux offset (BinOpJ op e1 e2) = BinApp1 (operToVecOp op) (aux offset e1) (aux offset e2)
    aux offset (UnOpJ NotJ e)    = UnApp1 D.Not (aux offset e)
    aux offset (UnOpJ FstJ e)    = aux offset e
    aux offset (UnOpJ SndJ e)    = aux (offset + 1) e
    aux _      (ConstJ v)        = Constant1 $ pVal v
    aux offset InputJ            = Column1 offset

operToCompOp :: O.Oper -> D.VecCompOp
operToCompOp op = case op of
  O.Eq   -> D.Eq
  O.Gt   -> D.Gt
  O.GtE  -> D.GtE
  O.Lt   -> D.Lt
  O.LtE  -> D.LtE
  _      -> error "VLPrimitives.operToComOp: not a comparison operator"

unique :: DBV -> GraphM r VL DBV
unique (DBV c _) = dbv $ insertNode $ UnOp Unique c

uniqueL :: DBV -> GraphM r VL DBV
uniqueL (DBV c _) = dbv $ insertNode $ UnOp UniqueL c

number :: DBV -> GraphM r VL DBV
number (DBV c _) = dbv $ insertNode $ UnOp Number c

numberL :: DBV -> GraphM r VL DBV
numberL (DBV c _) = dbv $ insertNode $ UnOp NumberL c

groupByKey :: DBV -> DBV -> GraphM r VL (DBV, DBV, PropVector)
groupByKey (DBV c1 _) (DBV c2 _) = do
                                  r <- insertNode $ BinOp GroupBy c1 c2
                                  r1 <- dbv $ insertNode $ UnOp R1 r
                                  r2 <- dbv $ insertNode $ UnOp R2 r
                                  r3 <- prop $ insertNode $ UnOp R3 r
                                  return (r1, r2, r3)

sortWith :: DBV -> DBV -> GraphM r VL (DBV, PropVector)
sortWith (DBV c1 _) (DBV c2 _) = do
                                  r <- insertNode $ BinOp SortWith c1 c2
                                  r1 <- dbv $ insertNode $ UnOp R1 r
                                  r2 <- prop $ insertNode $ UnOp R2 r
                                  return (r1, r2)

lengthA :: DBV -> GraphM r VL DBP
lengthA (DBV c _) = dbp $ insertNode $ UnOp LengthA c

lengthSeg :: DBV -> DBV -> GraphM r VL DBV
lengthSeg (DBV c1 _) (DBV c2 _) = dbv $ insertNode $ BinOp LengthSeg c1 c2

descToRename :: DBV -> GraphM r VL RenameVector
descToRename (DBV c _) = rename $ insertNode $ UnOp DescToRename c

distPrim :: DBP -> DBV -> GraphM r VL (DBV, PropVector)
distPrim (DBP c1 _) (DBV c2 _) = do
                                        r <- insertNode $ BinOp DistPrim c1 c2
                                        r1 <- dbv $ insertNode $ UnOp R1 r
                                        r2 <- prop $ insertNode $ UnOp R2 r
                                        return (r1, r2)

distDesc :: DBV -> DBV -> GraphM r VL (DBV, PropVector)
distDesc (DBV c1 _) (DBV c2 _) = do
                                        r <- insertNode $ BinOp DistDesc c1 c2
                                        r1 <- dbv $ insertNode $ UnOp R1 r
                                        r2 <- prop $ insertNode $ UnOp R2 r
                                        return (r1, r2)

distLift :: DBV -> DBV -> GraphM r VL (DBV, PropVector)
distLift (DBV c1 _) (DBV c2 _) = do
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

singletonDescr :: GraphM r VL DBV
singletonDescr = dbv $ insertNode $ NullaryOp SingletonDescr

append :: DBV -> DBV -> GraphM r VL (DBV, RenameVector, RenameVector)
append (DBV c1 _) (DBV c2 _) = do
                                r <- insertNode $ BinOp Append c1 c2
                                r1 <- dbv $ insertNode $ UnOp R1 r
                                r2 <- rename $ insertNode $ UnOp R2 r
                                r3 <- rename $ insertNode $ UnOp R3 r
                                return (r1, r2, r3)

segment :: DBV -> GraphM r VL DBV
segment (DBV c _) = dbv $ insertNode $ UnOp Segment c

unsegment :: DBV -> GraphM r VL DBV
unsegment (DBV c _) = dbv $ insertNode $ UnOp Unsegment c

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

compExpr2 :: O.Oper -> DBP -> DBP -> GraphM r VL DBP
compExpr2 o (DBP c1 _) (DBP c2 _) = dbp
                                    $ insertNode
                                    $ BinOp (CompExpr2 (BinApp2 (operToVecOp o) (Column2Left $ L 1) (Column2Right $ R 1))) c1 c2

compExpr2L :: O.Oper -> DBV -> DBV -> GraphM r VL DBV
compExpr2L o (DBV c1 _) (DBV c2 _) = dbv
                                     $ insertNode
                                     $ BinOp (CompExpr2L (BinApp2 (operToVecOp o) (Column2Left $ L 1) (Column2Right $ R 1))) c1 c2

vecSum :: Ty.Type -> DBV -> GraphM r VL DBP
vecSum ty (DBV c _) = dbp $ insertNode $ UnOp (VecSum (typeToVLType ty)) c

vecAvg :: DBV -> GraphM r VL DBP
vecAvg (DBV c _) = dbp $ insertNode $ UnOp VecAvg c

vecSumLift :: DBV -> DBV -> GraphM r VL DBV
vecSumLift (DBV c1 _) (DBV c2 _) = dbv $ insertNode $ BinOp VecSumL c1 c2

vecAvgLift :: DBV -> DBV -> GraphM r VL DBV
vecAvgLift (DBV c1 _) (DBV c2 _) = dbv $ insertNode $ BinOp VecAvgL c1 c2

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
                                        r <- insertNode $ BinOp (SelectPos (operToCompOp op)) c1 c2
                                        r1 <- dbv $ insertNode $ UnOp R1 r
                                        r2 <- rename $ insertNode $ UnOp R2 r
                                        return (r1, r2)

selectPos1 :: DBV -> O.Oper -> Nat -> GraphM r VL (DBV, RenameVector)
selectPos1 (DBV c1 _) op posConst = do
                                        r <- insertNode $ UnOp (SelectPos1 (operToCompOp op) posConst) c1
                                        r1 <- dbv $ insertNode $ UnOp R1 r
                                        r2 <- rename $ insertNode $ UnOp R2 r
                                        return (r1, r2)

selectPosLift :: DBV -> O.Oper -> DBV -> GraphM r VL (DBV, RenameVector)
selectPosLift (DBV c1 _) op (DBV c2 _) = do
                                          r <- insertNode $ BinOp (SelectPosL (operToCompOp op)) c1 c2
                                          r1 <- dbv $ insertNode $ UnOp R1 r
                                          r2 <- rename $ insertNode $ UnOp R2 r
                                          return (r1, r2)

selectPos1Lift :: DBV -> O.Oper -> Nat -> GraphM r VL (DBV, RenameVector)
selectPos1Lift (DBV c1 _) op posConst = do
                                          r <- insertNode $ UnOp (SelectPos1L (operToCompOp op) posConst) c1
                                          r1 <- dbv $ insertNode $ UnOp R1 r
                                          r2 <- rename $ insertNode $ UnOp R2 r
                                          return (r1, r2)

vlProject :: DBV -> [Expr1] -> GraphM r VL DBV
vlProject (DBV c _) projs = dbv $ insertNode $ UnOp (VLProject projs) c

vlProjectA :: DBP -> [Expr1] -> GraphM r VL DBP
vlProjectA (DBP c _) projs = dbp $ insertNode $ UnOp (VLProjectA projs) c

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
                              
cartProduct :: DBV -> DBV -> GraphM r VL (DBV, PropVector, PropVector)
cartProduct (DBV c1 _) (DBV c2 _) = do
  r  <- insertNode $ BinOp CartProduct c1 c2
  r1 <- dbv $ insertNode $ UnOp R1 r
  r2 <- prop $ insertNode $ UnOp R2 r
  r3 <- prop $ insertNode $ UnOp R3 r
  return (r1, r2, r3)
  
cartProductL :: DBV -> DBV -> GraphM r VL (DBV, PropVector, PropVector)
cartProductL (DBV c1 _) (DBV c2 _) = do
  r  <- insertNode $ BinOp CartProductL c1 c2
  r1 <- dbv $ insertNode $ UnOp R1 r
  r2 <- prop $ insertNode $ UnOp R2 r
  r3 <- prop $ insertNode $ UnOp R3 r
  return (r1, r2, r3)
  
equiJoin :: JoinExpr -> JoinExpr -> DBV -> DBV -> GraphM r VL (DBV, PropVector, PropVector)
equiJoin e1 e2 (DBV c1 _) (DBV c2 _) = do
  let e1' = joinExpr e1
      e2' = joinExpr e2
  r  <- insertNode $ BinOp (EquiJoin e1' e2') c1 c2
  r1 <- dbv $ insertNode $ UnOp R1 r
  r2 <- prop $ insertNode $ UnOp R2 r
  r3 <- prop $ insertNode $ UnOp R3 r
  return (r1, r2, r3)

equiJoinL :: JoinExpr -> JoinExpr -> DBV -> DBV -> GraphM r VL (DBV, PropVector, PropVector)
equiJoinL e1 e2 (DBV c1 _) (DBV c2 _) = do
  let e1' = joinExpr e1
      e2' = joinExpr e2
  r  <- insertNode $ BinOp (EquiJoinL e1' e2') c1 c2
  r1 <- dbv $ insertNode $ UnOp R1 r
  r2 <- prop $ insertNode $ UnOp R2 r
  r3 <- prop $ insertNode $ UnOp R3 r
  return (r1, r2, r3)

semiJoin :: JoinExpr -> JoinExpr -> DBV -> DBV -> GraphM r VL (DBV, RenameVector)
semiJoin e1 e2 (DBV c1 _) (DBV c2 _) = do
  let e1' = joinExpr e1
      e2' = joinExpr e2
  r  <- insertNode $ BinOp (SemiJoin e1' e2') c1 c2
  r1 <- dbv $ insertNode $ UnOp R1 r
  r2 <- rename $ insertNode $ UnOp R2 r
  return (r1, r2)

semiJoinL :: JoinExpr -> JoinExpr -> DBV -> DBV -> GraphM r VL (DBV, RenameVector)
semiJoinL e1 e2 (DBV c1 _) (DBV c2 _) = do
  let e1' = joinExpr e1
      e2' = joinExpr e2
  r  <- insertNode $ BinOp (SemiJoinL e1' e2') c1 c2
  r1 <- dbv $ insertNode $ UnOp R1 r
  r2 <- rename $ insertNode $ UnOp R2 r
  return (r1, r2)

antiJoin :: JoinExpr -> JoinExpr -> DBV -> DBV -> GraphM r VL (DBV, RenameVector)
antiJoin e1 e2 (DBV c1 _) (DBV c2 _) = do
  let e1' = joinExpr e1
      e2' = joinExpr e2
  r  <- insertNode $ BinOp (AntiJoin e1' e2') c1 c2
  r1 <- dbv $ insertNode $ UnOp R1 r
  r2 <- rename $ insertNode $ UnOp R2 r
  return (r1, r2)

antiJoinL :: JoinExpr -> JoinExpr -> DBV -> DBV -> GraphM r VL (DBV, RenameVector)
antiJoinL e1 e2 (DBV c1 _) (DBV c2 _) = do
  let e1' = joinExpr e1
      e2' = joinExpr e2
  r  <- insertNode $ BinOp (AntiJoinL e1' e2') c1 c2
  r1 <- dbv $ insertNode $ UnOp R1 r
  r2 <- rename $ insertNode $ UnOp R2 r
  return (r1, r2)
  
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

singleton :: DBP -> GraphM r VL DBV
singleton (DBP c _) = dbv $ insertNode $ UnOp Singleton c

only :: DBV -> GraphM r VL DBP
only (DBV c _) = dbp $ insertNode $ UnOp Only c
