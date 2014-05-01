-- FIXME should be able to combine most of the functions        

{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Database.DSH.VL.VLPrimitives where

import qualified Database.DSH.Common.Lang as L
import qualified Database.DSH.Common.Type as Ty
import           Database.DSH.VL.Data.DBVector

import           Database.DSH.Impossible

import           Database.Algebra.Dag.Builder
import           Database.Algebra.Dag.Common
import           Database.DSH.VL.Lang                 hiding (DBCol)
import qualified Database.DSH.VL.Lang                 as D

dvec :: GraphM r a AlgNode -> GraphM r a DVec
dvec = fmap (flip DVec [])

pvec :: GraphM r a AlgNode -> GraphM r a PVec
pvec = fmap PVec

rvec :: GraphM r a AlgNode -> GraphM r a RVec
rvec = fmap RVec

emptyVL :: VL
emptyVL = NullaryOp $ TableRef "Null" [] (L.TableHints [] L.PossiblyEmpty)

mapSnd :: (b -> c) -> (a, b) -> (a, c)
mapSnd f (a, b) = (a, f b)

pVal :: L.Val -> VLVal
pVal (L.IntV i)    = VLInt i
pVal (L.BoolV b)   = VLBool b
pVal (L.StringV s) = VLString s
pVal (L.DoubleV d) = VLDouble d
pVal L.UnitV       = VLUnit
pVal _             = error "pVal: Not a supported value"

typeToVLType :: Ty.Type -> VLType
typeToVLType t = case t of
  Ty.IntT        -> D.Int
  Ty.BoolT       -> D.Bool
  Ty.StringT     -> D.String
  Ty.UnitT       -> D.Unit
  Ty.DoubleT     -> D.Double
  Ty.PairT t1 t2 -> D.Pair (typeToVLType t1) (typeToVLType t2)
  Ty.ListT t'    -> D.VLList (typeToVLType t')
  Ty.FunT _ _    -> error "VLPrimitives: Functions can not occur in operator plans"
  Ty.VarT _      -> error "VLPrimitives: Variables can not occur in operator plans"

----------------------------------------------------------------------------------
-- Convert join expressions into regular VL expressions

-- | Determine the horizontal relational schema width of a type
recordWidth :: Ty.Type -> Int
recordWidth t =
    case t of
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

joinExpr :: L.JoinExpr -> Expr1
joinExpr expr = offsetExpr $ aux expr
  where
    -- Construct expressions in a bottom-up way. For a given join
    -- expression, return the following: 
    -- pair accessors   -> column offset in the flat relational representation
    -- scalar operation -> corresponding VL expression
    aux :: L.JoinExpr -> ColExpr
    aux (L.BinOpJ _ op e1 e2)   = Expr $ BinApp1 op 
                                                 (offsetExpr $ aux e1) 
                                                 (offsetExpr $ aux e2)
    aux (L.UnOpJ _ L.NotJ e)    = Expr $ UnApp1 L.Not (offsetExpr $ aux e)
    aux (L.UnOpJ _ L.FstJ e)    = aux e
    aux (L.UnOpJ _ L.SndJ e)    = 
        case Ty.typeOf e of
            Ty.PairT t1 _ -> addOffset (recordWidth t1) (aux e)
            _             -> $impossible
    aux (L.ConstJ _ v)          = Expr $ Constant1 $ pVal v
    aux (L.InputJ _)            = Offset 0
  

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

vlAlign :: DVec -> DVec -> GraphM r VL (DVec, PVec)
vlAlign (DVec c1 _) (DVec c2 _) = do
                                        r <- insertNode $ BinOp Align c1 c2
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

vlLit :: L.Emptiness -> [Ty.Type] -> [[VLVal]] -> GraphM r VL DVec
vlLit em tys vals = dvec $ insertNode $ NullaryOp $ Lit em (map typeToVLType tys) vals

vlTableRef :: String -> [VLColumn] -> L.TableHints -> GraphM r VL DVec
vlTableRef n tys hs = dvec $ insertNode $ NullaryOp $ TableRef n tys hs

vlUnExpr :: L.ScalarUnOp -> DVec -> GraphM r VL DVec
vlUnExpr o (DVec c _) =
    dvec $ insertNode $ UnOp (Project [UnApp1 o (Column1 1)]) c

vlBinExpr :: L.ScalarBinOp -> DVec -> DVec -> GraphM r VL DVec
vlBinExpr o (DVec c1 _) (DVec c2 _) = dvec
                                     $ insertNode
                                     $ BinOp (BinExpr (BinApp2 o (Column2Left $ L 1) (Column2Right $ R 1))) c1 c2

vlSelectPos :: DVec -> L.ScalarBinOp -> DVec -> GraphM r VL (DVec, RVec)
vlSelectPos (DVec c1 _) op (DVec c2 _) = do
                                        r <- insertNode $ BinOp (SelectPos op) c1 c2
                                        r1 <- dvec $ insertNode $ UnOp R1 r
                                        r2 <- rvec $ insertNode $ UnOp R2 r
                                        return (r1, r2)

vlSelectPos1 :: DVec -> L.ScalarBinOp -> Nat -> GraphM r VL (DVec, RVec)
vlSelectPos1 (DVec c1 _) op posConst = do
                                        r <- insertNode $ UnOp (SelectPos1 op posConst) c1
                                        r1 <- dvec $ insertNode $ UnOp R1 r
                                        r2 <- rvec $ insertNode $ UnOp R2 r
                                        return (r1, r2)

vlSelectPosS :: DVec -> L.ScalarBinOp -> DVec -> GraphM r VL (DVec, RVec)
vlSelectPosS (DVec c1 _) op (DVec c2 _) = do
                                          r <- insertNode $ BinOp (SelectPosS op) c1 c2
                                          r1 <- dvec $ insertNode $ UnOp R1 r
                                          r2 <- rvec $ insertNode $ UnOp R2 r
                                          return (r1, r2)

vlSelectPos1S :: DVec -> L.ScalarBinOp -> Nat -> GraphM r VL (DVec, RVec)
vlSelectPos1S (DVec c1 _) op posConst = do
                                          r <- insertNode $ UnOp (SelectPos1S op posConst) c1
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
  
vlEquiJoin :: L.JoinExpr -> L.JoinExpr -> DVec -> DVec -> GraphM r VL (DVec, PVec, PVec)
vlEquiJoin e1 e2 (DVec c1 _) (DVec c2 _) = do
  let e1' = joinExpr e1
      e2' = joinExpr e2
  r  <- insertNode $ BinOp (EquiJoin e1' e2') c1 c2
  r1 <- dvec $ insertNode $ UnOp R1 r
  r2 <- pvec $ insertNode $ UnOp R2 r
  r3 <- pvec $ insertNode $ UnOp R3 r
  return (r1, r2, r3)

vlEquiJoinS :: L.JoinExpr -> L.JoinExpr -> DVec -> DVec -> GraphM r VL (DVec, PVec, PVec)
vlEquiJoinS e1 e2 (DVec c1 _) (DVec c2 _) = do
  let e1' = joinExpr e1
      e2' = joinExpr e2
  r  <- insertNode $ BinOp (EquiJoinS e1' e2') c1 c2
  r1 <- dvec $ insertNode $ UnOp R1 r
  r2 <- pvec $ insertNode $ UnOp R2 r
  r3 <- pvec $ insertNode $ UnOp R3 r
  return (r1, r2, r3)

vlNestJoinS :: L.JoinExpr -> L.JoinExpr -> DVec -> DVec -> GraphM r VL (DVec, PVec)
vlNestJoinS e1 e2 (DVec c1 _) (DVec c2 _) = do
    let e1' = joinExpr e1
        e2' = joinExpr e2
    r  <- insertNode $ BinOp (NestJoinS e1' e2') c1 c2
    r1 <- dvec $ insertNode $ UnOp R1 r
    r2 <- pvec $ insertNode $ UnOp R2 r
    return (r1, r2)
    
vlNestProductS :: DVec -> DVec -> GraphM r VL (DVec, PVec)
vlNestProductS (DVec c1 _) (DVec c2 _) = do
    r <- insertNode $ BinOp NestProductS c1 c2
    r1 <- dvec $ insertNode $ UnOp R1 r
    r2 <- pvec $ insertNode $ UnOp R2 r
    return (r1, r2)
     
vlSemiJoin :: L.JoinExpr -> L.JoinExpr -> DVec -> DVec -> GraphM r VL (DVec, RVec)
vlSemiJoin e1 e2 (DVec c1 _) (DVec c2 _) = do
  let e1' = joinExpr e1
      e2' = joinExpr e2
  r  <- insertNode $ BinOp (SemiJoin e1' e2') c1 c2
  r1 <- dvec $ insertNode $ UnOp R1 r
  r2 <- rvec $ insertNode $ UnOp R2 r
  return (r1, r2)

vlSemiJoinS :: L.JoinExpr -> L.JoinExpr -> DVec -> DVec -> GraphM r VL (DVec, RVec)
vlSemiJoinS e1 e2 (DVec c1 _) (DVec c2 _) = do
  let e1' = joinExpr e1
      e2' = joinExpr e2
  r  <- insertNode $ BinOp (SemiJoinS e1' e2') c1 c2
  r1 <- dvec $ insertNode $ UnOp R1 r
  r2 <- rvec $ insertNode $ UnOp R2 r
  return (r1, r2)

vlAntiJoin :: L.JoinExpr -> L.JoinExpr -> DVec -> DVec -> GraphM r VL (DVec, RVec)
vlAntiJoin e1 e2 (DVec c1 _) (DVec c2 _) = do
  let e1' = joinExpr e1
      e2' = joinExpr e2
  r  <- insertNode $ BinOp (AntiJoin e1' e2') c1 c2
  r1 <- dvec $ insertNode $ UnOp R1 r
  r2 <- rvec $ insertNode $ UnOp R2 r
  return (r1, r2)

vlAntiJoinS :: L.JoinExpr -> L.JoinExpr -> DVec -> DVec -> GraphM r VL (DVec, RVec)
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

vlTranspose :: DVec -> GraphM r VL (DVec, DVec)
vlTranspose (DVec qi _) = do
    r  <- insertNode $ UnOp Transpose qi
    r1 <- dvec $ insertNode $ UnOp R1 r
    r2 <- dvec $ insertNode $ UnOp R2 r
    return (r1, r2)

vlTransposeS :: DVec -> DVec -> GraphM r VL (DVec, DVec)
vlTransposeS (DVec qo _) (DVec qi _) = do
    r <- insertNode $ BinOp TransposeS qo qi
    r1 <- dvec $ insertNode $ UnOp R1 r
    r2 <- dvec $ insertNode $ UnOp R2 r
    return (r1, r2)

vlReshape :: Integer -> DVec -> GraphM r VL (DVec, DVec)
vlReshape n (DVec q _) = do
    r <- insertNode $ UnOp (Reshape n) q
    r1 <- dvec $ insertNode $ UnOp R1 r
    r2 <- dvec $ insertNode $ UnOp R2 r
    return (r1, r2)

vlReshapeS :: Integer -> DVec -> GraphM r VL (DVec, DVec)
vlReshapeS n (DVec qi _) = do
    r <- insertNode $ UnOp (ReshapeS n) qi
    r1 <- dvec $ insertNode $ UnOp R1 r
    r2 <- dvec $ insertNode $ UnOp R2 r
    return (r1, r2)
