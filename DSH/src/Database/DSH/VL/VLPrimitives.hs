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

dvec :: GraphM r a AlgNode -> GraphM r a DVec
dvec = fmap (flip DVec [])

pvec :: GraphM r a AlgNode -> GraphM r a PVec
pvec = fmap PVec

rvec :: GraphM r a AlgNode -> GraphM r a RVec
rvec = fmap RVec

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

unique :: DVec -> GraphM r VL DVec
unique (DVec c _) = dvec $ insertNode $ UnOp Unique c

uniqueL :: DVec -> GraphM r VL DVec
uniqueL (DVec c _) = dvec $ insertNode $ UnOp UniqueL c

number :: DVec -> GraphM r VL DVec
number (DVec c _) = dvec $ insertNode $ UnOp Number c

numberL :: DVec -> GraphM r VL DVec
numberL (DVec c _) = dvec $ insertNode $ UnOp NumberL c

groupByKey :: DVec -> DVec -> GraphM r VL (DVec, DVec, PVec)
groupByKey (DVec c1 _) (DVec c2 _) = do
                                  r <- insertNode $ BinOp GroupBy c1 c2
                                  r1 <- dvec $ insertNode $ UnOp R1 r
                                  r2 <- dvec $ insertNode $ UnOp R2 r
                                  r3 <- pvec $ insertNode $ UnOp R3 r
                                  return (r1, r2, r3)

sortWith :: DVec -> DVec -> GraphM r VL (DVec, PVec)
sortWith (DVec c1 _) (DVec c2 _) = do
                                  r <- insertNode $ BinOp SortWith c1 c2
                                  r1 <- dvec $ insertNode $ UnOp R1 r
                                  r2 <- pvec $ insertNode $ UnOp R2 r
                                  return (r1, r2)

lengthA :: DVec -> GraphM r VL DVec
lengthA (DVec c _) = dvec $ insertNode $ UnOp LengthA c

lengthSeg :: DVec -> DVec -> GraphM r VL DVec
lengthSeg (DVec c1 _) (DVec c2 _) = dvec $ insertNode $ BinOp LengthSeg c1 c2

descToRename :: DVec -> GraphM r VL RVec
descToRename (DVec c _) = rvec $ insertNode $ UnOp DescToRename c

distPrim :: DVec -> DVec -> GraphM r VL (DVec, PVec)
distPrim (DVec c1 _) (DVec c2 _) = do
                                        r <- insertNode $ BinOp DistPrim c1 c2
                                        r1 <- dvec $ insertNode $ UnOp R1 r
                                        r2 <- pvec $ insertNode $ UnOp R2 r
                                        return (r1, r2)

distDesc :: DVec -> DVec -> GraphM r VL (DVec, PVec)
distDesc (DVec c1 _) (DVec c2 _) = do
                                        r <- insertNode $ BinOp DistDesc c1 c2
                                        r1 <- dvec $ insertNode $ UnOp R1 r
                                        r2 <- pvec $ insertNode $ UnOp R2 r
                                        return (r1, r2)

distLift :: DVec -> DVec -> GraphM r VL (DVec, PVec)
distLift (DVec c1 _) (DVec c2 _) = do
                                        r <- insertNode $ BinOp DistLift c1 c2
                                        r1 <- dvec $ insertNode $ UnOp R1 r
                                        r2 <- pvec $ insertNode $ UnOp R2 r
                                        return (r1, r2)

-- | pvecRvec uses a propagation vector to rename a vector (no filtering or reordering).
propRename :: RVec -> DVec -> GraphM r VL DVec
propRename (RVec c1) (DVec c2 _) = dvec $ insertNode $ BinOp PropRename c1 c2

-- | pvecFilter uses a pvecagation vector to rvec and filter a vector (no reordering).
propFilter :: RVec -> DVec -> GraphM r VL (DVec, RVec)
propFilter (RVec c1) (DVec c2 _) = do
                                            r <- insertNode $ BinOp PropFilter c1 c2
                                            r1 <- dvec $ insertNode $ UnOp R1 r
                                            r2 <- rvec $ insertNode $ UnOp R2 r
                                            return (r1, r2)

-- | pvecReorder uses a pvecagation vector to rvec, filter and reorder a vector.
propReorder :: PVec -> DVec -> GraphM r VL (DVec, PVec)
propReorder (PVec c1) (DVec c2 _) = do
                                           r <- insertNode $ BinOp PropReorder c1 c2
                                           r1 <- dvec $ insertNode $ UnOp R1 r
                                           r2 <- pvec $ insertNode $ UnOp R2 r
                                           return (r1, r2)

singletonDescr :: GraphM r VL DVec
singletonDescr = dvec $ insertNode $ NullaryOp SingletonDescr

append :: DVec -> DVec -> GraphM r VL (DVec, RVec, RVec)
append (DVec c1 _) (DVec c2 _) = do
                                r <- insertNode $ BinOp Append c1 c2
                                r1 <- dvec $ insertNode $ UnOp R1 r
                                r2 <- rvec $ insertNode $ UnOp R2 r
                                r3 <- rvec $ insertNode $ UnOp R3 r
                                return (r1, r2, r3)

segment :: DVec -> GraphM r VL DVec
segment (DVec c _) = dvec $ insertNode $ UnOp Segment c

unsegment :: DVec -> GraphM r VL DVec
unsegment (DVec c _) = dvec $ insertNode $ UnOp Unsegment c

restrictVec :: DVec -> DVec -> GraphM r VL (DVec, RVec)
restrictVec (DVec c1 _) (DVec c2 _) = do
                                     r <- insertNode $ BinOp RestrictVec c1 c2
                                     r1 <- dvec $ insertNode $ UnOp R1 r
                                     r2 <- rvec $ insertNode $ UnOp R2 r
                                     return (r1, r2)

combineVec :: DVec -> DVec -> DVec -> GraphM r VL (DVec, RVec, RVec)
combineVec (DVec c1 _) (DVec c2 _) (DVec c3 _) = do
                                               r <- insertNode $ TerOp CombineVec c1 c2 c3
                                               r1 <- dvec $ insertNode $ UnOp R1 r
                                               r2 <- rvec $ insertNode $ UnOp R2 r
                                               r3 <- rvec $ insertNode $ UnOp R3 r
                                               return (r1, r2, r3)

constructLiteralValue :: [Ty.Type] -> [VLVal] -> GraphM r VL DVec
constructLiteralValue tys vals = dvec $ insertNode $ NullaryOp $ ConstructLiteralValue (map typeToVLType tys) vals

constructLiteralTable :: [Ty.Type] -> [[VLVal]] -> GraphM r VL DVec
constructLiteralTable tys vals = dvec $ insertNode $ NullaryOp $ ConstructLiteralTable (map typeToVLType tys) vals

tableRef :: String -> [TypedColumn] -> [Key] -> GraphM r VL DVec
tableRef n tys ks = dvec $ insertNode $ NullaryOp $ TableRef n ({-map (mapSnd typeToVLType)-} tys) ks

compExpr2 :: O.Oper -> DVec -> DVec -> GraphM r VL DVec
compExpr2 o (DVec c1 _) (DVec c2 _) = dvec
                                    $ insertNode
                                    $ BinOp (CompExpr2 (BinApp2 (operToVecOp o) (Column2Left $ L 1) (Column2Right $ R 1))) c1 c2

compExpr2L :: O.Oper -> DVec -> DVec -> GraphM r VL DVec
compExpr2L o (DVec c1 _) (DVec c2 _) = dvec
                                     $ insertNode
                                     $ BinOp (CompExpr2L (BinApp2 (operToVecOp o) (Column2Left $ L 1) (Column2Right $ R 1))) c1 c2

vecSum :: Ty.Type -> DVec -> GraphM r VL DVec
vecSum ty (DVec c _) = dvec $ insertNode $ UnOp (VecSum (typeToVLType ty)) c

vecAvg :: DVec -> GraphM r VL DVec
vecAvg (DVec c _) = dvec $ insertNode $ UnOp VecAvg c

vecSumLift :: DVec -> DVec -> GraphM r VL DVec
vecSumLift (DVec c1 _) (DVec c2 _) = dvec $ insertNode $ BinOp VecSumL c1 c2

vecAvgLift :: DVec -> DVec -> GraphM r VL DVec
vecAvgLift (DVec c1 _) (DVec c2 _) = dvec $ insertNode $ BinOp VecAvgL c1 c2

vecMin :: DVec -> GraphM r VL DVec
vecMin (DVec c _) = dvec $ insertNode $ UnOp VecMin c

vecMinLift :: DVec -> GraphM r VL DVec
vecMinLift (DVec c _) = dvec $ insertNode $ UnOp VecMinL c

vecMax :: DVec -> GraphM r VL DVec
vecMax (DVec c _) = dvec $ insertNode $ UnOp VecMax c

vecMaxLift :: DVec -> GraphM r VL DVec
vecMaxLift (DVec c _) = dvec $ insertNode $ UnOp VecMaxL c

selectPos :: DVec -> O.Oper -> DVec -> GraphM r VL (DVec, RVec)
selectPos (DVec c1 _) op (DVec c2 _) = do
                                        r <- insertNode $ BinOp (SelectPos (operToCompOp op)) c1 c2
                                        r1 <- dvec $ insertNode $ UnOp R1 r
                                        r2 <- rvec $ insertNode $ UnOp R2 r
                                        return (r1, r2)

selectPos1 :: DVec -> O.Oper -> Nat -> GraphM r VL (DVec, RVec)
selectPos1 (DVec c1 _) op posConst = do
                                        r <- insertNode $ UnOp (SelectPos1 (operToCompOp op) posConst) c1
                                        r1 <- dvec $ insertNode $ UnOp R1 r
                                        r2 <- rvec $ insertNode $ UnOp R2 r
                                        return (r1, r2)

selectPosLift :: DVec -> O.Oper -> DVec -> GraphM r VL (DVec, RVec)
selectPosLift (DVec c1 _) op (DVec c2 _) = do
                                          r <- insertNode $ BinOp (SelectPosL (operToCompOp op)) c1 c2
                                          r1 <- dvec $ insertNode $ UnOp R1 r
                                          r2 <- rvec $ insertNode $ UnOp R2 r
                                          return (r1, r2)

selectPos1Lift :: DVec -> O.Oper -> Nat -> GraphM r VL (DVec, RVec)
selectPos1Lift (DVec c1 _) op posConst = do
                                          r <- insertNode $ UnOp (SelectPos1L (operToCompOp op) posConst) c1
                                          r1 <- dvec $ insertNode $ UnOp R1 r
                                          r2 <- rvec $ insertNode $ UnOp R2 r
                                          return (r1, r2)

vlProject :: DVec -> [Expr1] -> GraphM r VL DVec
vlProject (DVec c _) projs = dvec $ insertNode $ UnOp (VLProject projs) c

vlProjectA :: DVec -> [Expr1] -> GraphM r VL DVec
vlProjectA (DVec c _) projs = dvec $ insertNode $ UnOp (VLProjectA projs) c

pairA :: DVec -> DVec -> GraphM r VL DVec
pairA (DVec c1 _) (DVec c2 _) = dvec $ insertNode $ BinOp PairA c1 c2

pairL :: DVec -> DVec -> GraphM r VL DVec
pairL (DVec c1 _) (DVec c2 _) = dvec $ insertNode $ BinOp PairL c1 c2

zipL :: DVec -> DVec -> GraphM r VL (DVec, RVec, RVec)
zipL (DVec c1 _) (DVec c2 _) = do
                              r <- insertNode $ BinOp ZipL c1 c2
                              r1 <- dvec $ insertNode $ UnOp R1 r
                              r2 <- rvec $ insertNode $ UnOp R2 r
                              r3 <- rvec $ insertNode $ UnOp R3 r
                              return (r1, r2, r3)
                              
cartProduct :: DVec -> DVec -> GraphM r VL (DVec, PVec, PVec)
cartProduct (DVec c1 _) (DVec c2 _) = do
  r  <- insertNode $ BinOp CartProduct c1 c2
  r1 <- dvec $ insertNode $ UnOp R1 r
  r2 <- pvec $ insertNode $ UnOp R2 r
  r3 <- pvec $ insertNode $ UnOp R3 r
  return (r1, r2, r3)
  
cartProductL :: DVec -> DVec -> GraphM r VL (DVec, PVec, PVec)
cartProductL (DVec c1 _) (DVec c2 _) = do
  r  <- insertNode $ BinOp CartProductL c1 c2
  r1 <- dvec $ insertNode $ UnOp R1 r
  r2 <- pvec $ insertNode $ UnOp R2 r
  r3 <- pvec $ insertNode $ UnOp R3 r
  return (r1, r2, r3)
  
equiJoin :: JoinExpr -> JoinExpr -> DVec -> DVec -> GraphM r VL (DVec, PVec, PVec)
equiJoin e1 e2 (DVec c1 _) (DVec c2 _) = do
  let e1' = joinExpr e1
      e2' = joinExpr e2
  r  <- insertNode $ BinOp (EquiJoin e1' e2') c1 c2
  r1 <- dvec $ insertNode $ UnOp R1 r
  r2 <- pvec $ insertNode $ UnOp R2 r
  r3 <- pvec $ insertNode $ UnOp R3 r
  return (r1, r2, r3)

equiJoinL :: JoinExpr -> JoinExpr -> DVec -> DVec -> GraphM r VL (DVec, PVec, PVec)
equiJoinL e1 e2 (DVec c1 _) (DVec c2 _) = do
  let e1' = joinExpr e1
      e2' = joinExpr e2
  r  <- insertNode $ BinOp (EquiJoinL e1' e2') c1 c2
  r1 <- dvec $ insertNode $ UnOp R1 r
  r2 <- pvec $ insertNode $ UnOp R2 r
  r3 <- pvec $ insertNode $ UnOp R3 r
  return (r1, r2, r3)

semiJoin :: JoinExpr -> JoinExpr -> DVec -> DVec -> GraphM r VL (DVec, RVec)
semiJoin e1 e2 (DVec c1 _) (DVec c2 _) = do
  let e1' = joinExpr e1
      e2' = joinExpr e2
  r  <- insertNode $ BinOp (SemiJoin e1' e2') c1 c2
  r1 <- dvec $ insertNode $ UnOp R1 r
  r2 <- rvec $ insertNode $ UnOp R2 r
  return (r1, r2)

semiJoinL :: JoinExpr -> JoinExpr -> DVec -> DVec -> GraphM r VL (DVec, RVec)
semiJoinL e1 e2 (DVec c1 _) (DVec c2 _) = do
  let e1' = joinExpr e1
      e2' = joinExpr e2
  r  <- insertNode $ BinOp (SemiJoinL e1' e2') c1 c2
  r1 <- dvec $ insertNode $ UnOp R1 r
  r2 <- rvec $ insertNode $ UnOp R2 r
  return (r1, r2)

antiJoin :: JoinExpr -> JoinExpr -> DVec -> DVec -> GraphM r VL (DVec, RVec)
antiJoin e1 e2 (DVec c1 _) (DVec c2 _) = do
  let e1' = joinExpr e1
      e2' = joinExpr e2
  r  <- insertNode $ BinOp (AntiJoin e1' e2') c1 c2
  r1 <- dvec $ insertNode $ UnOp R1 r
  r2 <- rvec $ insertNode $ UnOp R2 r
  return (r1, r2)

antiJoinL :: JoinExpr -> JoinExpr -> DVec -> DVec -> GraphM r VL (DVec, RVec)
antiJoinL e1 e2 (DVec c1 _) (DVec c2 _) = do
  let e1' = joinExpr e1
      e2' = joinExpr e2
  r  <- insertNode $ BinOp (AntiJoinL e1' e2') c1 c2
  r1 <- dvec $ insertNode $ UnOp R1 r
  r2 <- rvec $ insertNode $ UnOp R2 r
  return (r1, r2)
  
reverseA :: DVec -> GraphM r VL (DVec, PVec)
reverseA (DVec c _) = do
                      r <- insertNode $ UnOp ReverseA c
                      r1 <- dvec $ insertNode $ UnOp R1 r
                      r2 <- pvec $ insertNode $ UnOp R2 r
                      return (r1, r2)

reverseL :: DVec -> GraphM r VL (DVec, PVec)
reverseL (DVec c _) = do
                       r <- insertNode $ UnOp ReverseL c
                       r1 <- dvec $ insertNode $ UnOp R1 r
                       r2 <- pvec $ insertNode $ UnOp R2 r
                       return (r1, r2)

falsePositions :: DVec -> GraphM r VL DVec
falsePositions (DVec c _) = dvec $ insertNode $ UnOp FalsePositions c

singleton :: DVec -> GraphM r VL DVec
singleton (DVec c _) = dvec $ insertNode $ UnOp Singleton c

only :: DVec -> GraphM r VL DVec
only (DVec c _) = dvec $ insertNode $ UnOp Only c
