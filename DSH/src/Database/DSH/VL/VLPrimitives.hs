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

vlUnique :: DVec -> GraphM r VL DVec
vlUnique (DVec c _) = dvec $ insertNode $ UnOp Unique c

vlUniqueS :: DVec -> GraphM r VL DVec
vlUniqueS (DVec c _) = dvec $ insertNode $ UnOp UniqueS c

vlNumber :: DVec -> GraphM r VL DVec
vlNumber (DVec c _) = dvec $ insertNode $ UnOp Number c

vlNumberS :: DVec -> GraphM r VL DVec
vlNumberS (DVec c _) = dvec $ insertNode $ UnOp NumberS c

vlGroupBy :: DVec -> DVec -> GraphM r VL (DVec, DVec, PVec)
vlGroupBy (DVec c1 _) (DVec c2 _) = do
                                  r <- insertNode $ BinOp GroupBy c1 c2
                                  r1 <- dvec $ insertNode $ UnOp R1 r
                                  r2 <- dvec $ insertNode $ UnOp R2 r
                                  r3 <- pvec $ insertNode $ UnOp R3 r
                                  return (r1, r2, r3)

vlSort :: DVec -> DVec -> GraphM r VL (DVec, PVec)
vlSort (DVec c1 _) (DVec c2 _) = do
                                  r <- insertNode $ BinOp Sort c1 c2
                                  r1 <- dvec $ insertNode $ UnOp R1 r
                                  r2 <- pvec $ insertNode $ UnOp R2 r
                                  return (r1, r2)

vlAggr :: AggrFun -> DVec -> GraphM r VL DVec
vlAggr aFun (DVec c _) = dvec $ insertNode $ UnOp (Aggr aFun) c

vlAggrS :: AggrFun -> DVec -> DVec -> GraphM r VL DVec
vlAggrS aFun (DVec c1 _) (DVec c2 _) = dvec $ insertNode $ BinOp (AggrS aFun) c1 c2

vlDescToRename :: DVec -> GraphM r VL RVec
vlDescToRename (DVec c _) = rvec $ insertNode $ UnOp DescToRename c

vlDistPrim :: DVec -> DVec -> GraphM r VL (DVec, PVec)
vlDistPrim (DVec c1 _) (DVec c2 _) = do
                                        r <- insertNode $ BinOp DistPrim c1 c2
                                        r1 <- dvec $ insertNode $ UnOp R1 r
                                        r2 <- pvec $ insertNode $ UnOp R2 r
                                        return (r1, r2)

vlDistDesc :: DVec -> DVec -> GraphM r VL (DVec, PVec)
vlDistDesc (DVec c1 _) (DVec c2 _) = do
                                        r <- insertNode $ BinOp DistDesc c1 c2
                                        r1 <- dvec $ insertNode $ UnOp R1 r
                                        r2 <- pvec $ insertNode $ UnOp R2 r
                                        return (r1, r2)

vlDistSeg :: DVec -> DVec -> GraphM r VL (DVec, PVec)
vlDistSeg (DVec c1 _) (DVec c2 _) = do
                                        r <- insertNode $ BinOp DistSeg c1 c2
                                        r1 <- dvec $ insertNode $ UnOp R1 r
                                        r2 <- pvec $ insertNode $ UnOp R2 r
                                        return (r1, r2)

-- | pvecRvec uses a propagation vector to rename a vector (no filtering or reordering).
vlPropRename :: RVec -> DVec -> GraphM r VL DVec
vlPropRename (RVec c1) (DVec c2 _) = dvec $ insertNode $ BinOp PropRename c1 c2

-- | pvecFilter uses a pvecagation vector to rvec and filter a vector (no reordering).
vlPropFilter :: RVec -> DVec -> GraphM r VL (DVec, RVec)
vlPropFilter (RVec c1) (DVec c2 _) = do
                                            r <- insertNode $ BinOp PropFilter c1 c2
                                            r1 <- dvec $ insertNode $ UnOp R1 r
                                            r2 <- rvec $ insertNode $ UnOp R2 r
                                            return (r1, r2)

-- | pvecReorder uses a pvecagation vector to rvec, filter and reorder a vector.
vlPropReorder :: PVec -> DVec -> GraphM r VL (DVec, PVec)
vlPropReorder (PVec c1) (DVec c2 _) = do
                                           r <- insertNode $ BinOp PropReorder c1 c2
                                           r1 <- dvec $ insertNode $ UnOp R1 r
                                           r2 <- pvec $ insertNode $ UnOp R2 r
                                           return (r1, r2)

vlSingletonDescr :: GraphM r VL DVec
vlSingletonDescr = dvec $ insertNode $ NullaryOp SingletonDescr

vlAppend :: DVec -> DVec -> GraphM r VL (DVec, RVec, RVec)
vlAppend (DVec c1 _) (DVec c2 _) = do
                                r <- insertNode $ BinOp Append c1 c2
                                r1 <- dvec $ insertNode $ UnOp R1 r
                                r2 <- rvec $ insertNode $ UnOp R2 r
                                r3 <- rvec $ insertNode $ UnOp R3 r
                                return (r1, r2, r3)

vlSegment :: DVec -> GraphM r VL DVec
vlSegment (DVec c _) = dvec $ insertNode $ UnOp Segment c

vlUnsegment :: DVec -> GraphM r VL DVec
vlUnsegment (DVec c _) = dvec $ insertNode $ UnOp Unsegment c

vlRestrict :: DVec -> DVec -> GraphM r VL (DVec, RVec)
vlRestrict (DVec c1 _) (DVec c2 _) = do
                                     r <- insertNode $ BinOp Restrict c1 c2
                                     r1 <- dvec $ insertNode $ UnOp R1 r
                                     r2 <- rvec $ insertNode $ UnOp R2 r
                                     return (r1, r2)

vlCombine :: DVec -> DVec -> DVec -> GraphM r VL (DVec, RVec, RVec)
vlCombine (DVec c1 _) (DVec c2 _) (DVec c3 _) = do
                                               r <- insertNode $ TerOp Combine c1 c2 c3
                                               r1 <- dvec $ insertNode $ UnOp R1 r
                                               r2 <- rvec $ insertNode $ UnOp R2 r
                                               r3 <- rvec $ insertNode $ UnOp R3 r
                                               return (r1, r2, r3)

vlLit :: [Ty.Type] -> [[VLVal]] -> GraphM r VL DVec
vlLit tys vals = dvec $ insertNode $ NullaryOp $ Lit (map typeToVLType tys) vals

vlTableRef :: String -> [TypedColumn] -> [Key] -> GraphM r VL DVec
vlTableRef n tys ks = dvec $ insertNode $ NullaryOp $ TableRef n ({-map (mapSnd typeToVLType)-} tys) ks

vlBinExpr :: O.Oper -> DVec -> DVec -> GraphM r VL DVec
vlBinExpr o (DVec c1 _) (DVec c2 _) = dvec
                                     $ insertNode
                                     $ BinOp (BinExpr (BinApp2 (operToVecOp o) (Column2Left $ L 1) (Column2Right $ R 1))) c1 c2

vlSelectPos :: DVec -> O.Oper -> DVec -> GraphM r VL (DVec, RVec)
vlSelectPos (DVec c1 _) op (DVec c2 _) = do
                                        r <- insertNode $ BinOp (SelectPos (operToCompOp op)) c1 c2
                                        r1 <- dvec $ insertNode $ UnOp R1 r
                                        r2 <- rvec $ insertNode $ UnOp R2 r
                                        return (r1, r2)

vlSelectPos1 :: DVec -> O.Oper -> Nat -> GraphM r VL (DVec, RVec)
vlSelectPos1 (DVec c1 _) op posConst = do
                                        r <- insertNode $ UnOp (SelectPos1 (operToCompOp op) posConst) c1
                                        r1 <- dvec $ insertNode $ UnOp R1 r
                                        r2 <- rvec $ insertNode $ UnOp R2 r
                                        return (r1, r2)

vlSelectPosS :: DVec -> O.Oper -> DVec -> GraphM r VL (DVec, RVec)
vlSelectPosS (DVec c1 _) op (DVec c2 _) = do
                                          r <- insertNode $ BinOp (SelectPosS (operToCompOp op)) c1 c2
                                          r1 <- dvec $ insertNode $ UnOp R1 r
                                          r2 <- rvec $ insertNode $ UnOp R2 r
                                          return (r1, r2)

vlSelectPos1S :: DVec -> O.Oper -> Nat -> GraphM r VL (DVec, RVec)
vlSelectPos1S (DVec c1 _) op posConst = do
                                          r <- insertNode $ UnOp (SelectPos1S (operToCompOp op) posConst) c1
                                          r1 <- dvec $ insertNode $ UnOp R1 r
                                          r2 <- rvec $ insertNode $ UnOp R2 r
                                          return (r1, r2)

vlProject :: DVec -> [Expr1] -> GraphM r VL DVec
vlProject (DVec c _) projs = dvec $ insertNode $ UnOp (Project projs) c

vlZip :: DVec -> DVec -> GraphM r VL DVec
vlZip (DVec c1 _) (DVec c2 _) = dvec $ insertNode $ BinOp Zip c1 c2

vlZipS :: DVec -> DVec -> GraphM r VL (DVec, RVec, RVec)
vlZipS (DVec c1 _) (DVec c2 _) = do
                              r <- insertNode $ BinOp ZipS c1 c2
                              r1 <- dvec $ insertNode $ UnOp R1 r
                              r2 <- rvec $ insertNode $ UnOp R2 r
                              r3 <- rvec $ insertNode $ UnOp R3 r
                              return (r1, r2, r3)
                              
vlCartProduct :: DVec -> DVec -> GraphM r VL (DVec, PVec, PVec)
vlCartProduct (DVec c1 _) (DVec c2 _) = do
  r  <- insertNode $ BinOp CartProduct c1 c2
  r1 <- dvec $ insertNode $ UnOp R1 r
  r2 <- pvec $ insertNode $ UnOp R2 r
  r3 <- pvec $ insertNode $ UnOp R3 r
  return (r1, r2, r3)
  
vlCartProductS :: DVec -> DVec -> GraphM r VL (DVec, PVec, PVec)
vlCartProductS (DVec c1 _) (DVec c2 _) = do
  r  <- insertNode $ BinOp CartProductS c1 c2
  r1 <- dvec $ insertNode $ UnOp R1 r
  r2 <- pvec $ insertNode $ UnOp R2 r
  r3 <- pvec $ insertNode $ UnOp R3 r
  return (r1, r2, r3)
  
vlEquiJoin :: JoinExpr -> JoinExpr -> DVec -> DVec -> GraphM r VL (DVec, PVec, PVec)
vlEquiJoin e1 e2 (DVec c1 _) (DVec c2 _) = do
  let e1' = joinExpr e1
      e2' = joinExpr e2
  r  <- insertNode $ BinOp (EquiJoin e1' e2') c1 c2
  r1 <- dvec $ insertNode $ UnOp R1 r
  r2 <- pvec $ insertNode $ UnOp R2 r
  r3 <- pvec $ insertNode $ UnOp R3 r
  return (r1, r2, r3)

vlEquiJoinS :: JoinExpr -> JoinExpr -> DVec -> DVec -> GraphM r VL (DVec, PVec, PVec)
vlEquiJoinS e1 e2 (DVec c1 _) (DVec c2 _) = do
  let e1' = joinExpr e1
      e2' = joinExpr e2
  r  <- insertNode $ BinOp (EquiJoinS e1' e2') c1 c2
  r1 <- dvec $ insertNode $ UnOp R1 r
  r2 <- pvec $ insertNode $ UnOp R2 r
  r3 <- pvec $ insertNode $ UnOp R3 r
  return (r1, r2, r3)

vlSemiJoin :: JoinExpr -> JoinExpr -> DVec -> DVec -> GraphM r VL (DVec, RVec)
vlSemiJoin e1 e2 (DVec c1 _) (DVec c2 _) = do
  let e1' = joinExpr e1
      e2' = joinExpr e2
  r  <- insertNode $ BinOp (SemiJoin e1' e2') c1 c2
  r1 <- dvec $ insertNode $ UnOp R1 r
  r2 <- rvec $ insertNode $ UnOp R2 r
  return (r1, r2)

vlSemiJoinS :: JoinExpr -> JoinExpr -> DVec -> DVec -> GraphM r VL (DVec, RVec)
vlSemiJoinS e1 e2 (DVec c1 _) (DVec c2 _) = do
  let e1' = joinExpr e1
      e2' = joinExpr e2
  r  <- insertNode $ BinOp (SemiJoinS e1' e2') c1 c2
  r1 <- dvec $ insertNode $ UnOp R1 r
  r2 <- rvec $ insertNode $ UnOp R2 r
  return (r1, r2)

vlAntiJoin :: JoinExpr -> JoinExpr -> DVec -> DVec -> GraphM r VL (DVec, RVec)
vlAntiJoin e1 e2 (DVec c1 _) (DVec c2 _) = do
  let e1' = joinExpr e1
      e2' = joinExpr e2
  r  <- insertNode $ BinOp (AntiJoin e1' e2') c1 c2
  r1 <- dvec $ insertNode $ UnOp R1 r
  r2 <- rvec $ insertNode $ UnOp R2 r
  return (r1, r2)

vlAntiJoinS :: JoinExpr -> JoinExpr -> DVec -> DVec -> GraphM r VL (DVec, RVec)
vlAntiJoinS e1 e2 (DVec c1 _) (DVec c2 _) = do
  let e1' = joinExpr e1
      e2' = joinExpr e2
  r  <- insertNode $ BinOp (AntiJoinS e1' e2') c1 c2
  r1 <- dvec $ insertNode $ UnOp R1 r
  r2 <- rvec $ insertNode $ UnOp R2 r
  return (r1, r2)
  
vlReverse :: DVec -> GraphM r VL (DVec, PVec)
vlReverse (DVec c _) = do
                      r <- insertNode $ UnOp Reverse c
                      r1 <- dvec $ insertNode $ UnOp R1 r
                      r2 <- pvec $ insertNode $ UnOp R2 r
                      return (r1, r2)

vlReverseS :: DVec -> GraphM r VL (DVec, PVec)
vlReverseS (DVec c _) = do
                       r <- insertNode $ UnOp ReverseS c
                       r1 <- dvec $ insertNode $ UnOp R1 r
                       r2 <- pvec $ insertNode $ UnOp R2 r
                       return (r1, r2)

vlFalsePositions :: DVec -> GraphM r VL DVec
vlFalsePositions (DVec c _) = dvec $ insertNode $ UnOp FalsePositions c

vlSingleton :: DVec -> GraphM r VL DVec
vlSingleton (DVec c _) = dvec $ insertNode $ UnOp Singleton c

vlOnly :: DVec -> GraphM r VL DVec
vlOnly (DVec c _) = dvec $ insertNode $ UnOp Only c
