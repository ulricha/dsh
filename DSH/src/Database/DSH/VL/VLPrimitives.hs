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

operToCompOp :: O.Oper -> D.VecCompOp
operToCompOp op = case op of
  O.Eq   -> D.Eq
  O.Gt   -> D.Gt
  O.GtE  -> D.GtE
  O.Lt   -> D.Lt
  O.LtE  -> D.LtE
  _      -> error "VLPrimitives.operToComOp: not a comparison operator"

----------------------------------------------------------------------------------
-- Convert join expressions into regular VL expressions

-- | Determine the horizontal relational schema width of a type
recordWidth :: Ty.Type -> Int
recordWidth t =
    case t of
        Ty.NatT        -> 1
        Ty.IntT        -> 1
        Ty.BoolT       -> 1
        Ty.DoubleT     -> 1
        Ty.StringT     -> 1
        Ty.UnitT       -> 1
        -- WTF is a VarT
        Ty.VarT _      -> $impossible
        Ty.FunT _ _    -> $impossible
        Ty.PairT t1 t2 -> recordWidth t1 + recordWidth t2
        Ty.ListT _     -> 0

data ColExpr = Offset Int | Expr Expr1

-- | If the child expressions are tuple operators which only give the
-- column offset, convert it into a proper expression first.
offsetExpr :: ColExpr -> Expr1
offsetExpr (Offset o) = Column1 $ o + 1
offsetExpr (Expr e)   = e

addOffset :: Int -> ColExpr -> ColExpr
addOffset i (Expr e)   = $impossible
addOffset i (Offset o) = Offset $ o + i

joinExpr :: JoinExpr -> Expr1
joinExpr expr = offsetExpr $ aux expr
  where
    -- Construct expressions in a bottom-up way. For a given join
    -- expression, return the following: 
    -- pair accessors   -> column offset in the flat relational representation
    -- scalar operation -> corresponding VL expression
    aux :: JoinExpr -> ColExpr
    aux (BinOpJ _ op e1 e2) = Expr $ BinApp1 (operToVecOp op) 
                                             (offsetExpr $ aux e1) 
                                             (offsetExpr $ aux e2)
    aux (UnOpJ _ NotJ e)    = Expr $ UnApp1 D.Not (offsetExpr $ aux e)
    aux (UnOpJ _ FstJ e)    = aux e
    aux (UnOpJ _ SndJ e)    = 
        case Ty.typeOf e of
            Ty.PairT t1 _ -> addOffset (recordWidth t1) (aux e)
            _             -> $impossible
    aux (ConstJ _ v)        = Expr $ Constant1 $ pVal v
    aux (InputJ _)          = Offset 0
  

----------------------------------------------------------------------------------
-- DAG constructor functions for VL operators
  
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
vlTableRef n tys ks = dvec $ insertNode $ NullaryOp $ TableRef n tys ks

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
                              
vlCartProduct :: DVec -> DVec -> GraphM r VL (DVec, RVec, PVec)
vlCartProduct (DVec c1 _) (DVec c2 _) = do
  r  <- insertNode $ BinOp CartProduct c1 c2
  r1 <- dvec $ insertNode $ UnOp R1 r
  r2 <- rvec $ insertNode $ UnOp R2 r
  r3 <- pvec $ insertNode $ UnOp R3 r
  return (r1, r2, r3)
  
vlCartProductS :: DVec -> DVec -> GraphM r VL (DVec, RVec, PVec)
vlCartProductS (DVec c1 _) (DVec c2 _) = do
  r  <- insertNode $ BinOp CartProductS c1 c2
  r1 <- dvec $ insertNode $ UnOp R1 r
  r2 <- rvec $ insertNode $ UnOp R2 r
  r3 <- pvec $ insertNode $ UnOp R3 r
  return (r1, r2, r3)
  
vlEquiJoin :: JoinExpr -> JoinExpr -> DVec -> DVec -> GraphM r VL (DVec, RVec, PVec)
vlEquiJoin e1 e2 (DVec c1 _) (DVec c2 _) = do
  let e1' = joinExpr e1
      e2' = joinExpr e2
  r  <- insertNode $ BinOp (EquiJoin e1' e2') c1 c2
  r1 <- dvec $ insertNode $ UnOp R1 r
  r2 <- rvec $ insertNode $ UnOp R2 r
  r3 <- pvec $ insertNode $ UnOp R3 r
  return (r1, r2, r3)

vlEquiJoinS :: JoinExpr -> JoinExpr -> DVec -> DVec -> GraphM r VL (DVec, RVec, PVec)
vlEquiJoinS e1 e2 (DVec c1 _) (DVec c2 _) = do
  let e1' = joinExpr e1
      e2' = joinExpr e2
  r  <- insertNode $ BinOp (EquiJoinS e1' e2') c1 c2
  r1 <- dvec $ insertNode $ UnOp R1 r
  r2 <- rvec $ insertNode $ UnOp R2 r
  r3 <- pvec $ insertNode $ UnOp R3 r
  return (r1, r2, r3)

vlNestJoinS :: JoinExpr -> JoinExpr -> DVec -> DVec -> GraphM r VL (DVec, RVec, PVec)
vlNestJoinS e1 e2 (DVec c1 _) (DVec c2 _) = do
    let e1' = joinExpr e1
        e2' = joinExpr e2
    r  <- insertNode $ BinOp (NestJoinS e1' e2') c1 c2
    r1 <- dvec $ insertNode $ UnOp R1 r
    r2 <- rvec $ insertNode $ UnOp R2 r
    r3 <- pvec $ insertNode $ UnOp R3 r
    return (r1, r2, r3)
    

vlNestProductS :: DVec -> DVec -> GraphM r VL (DVec, RVec, PVec)
vlNestProductS (DVec c1 _) (DVec c2 _) = do
    r <- insertNode $ BinOp NestProductS c1 c2
    r1 <- dvec $ insertNode $ UnOp R1 r
    r2 <- rvec $ insertNode $ UnOp R2 r
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
