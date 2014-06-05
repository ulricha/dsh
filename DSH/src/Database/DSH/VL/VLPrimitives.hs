{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Database.DSH.VL.VLPrimitives where

import qualified Database.DSH.Common.Lang      as L
import qualified Database.DSH.Common.Type      as Ty
import           Database.DSH.VL.Vector

import           Database.DSH.Impossible

import           Database.Algebra.Dag.Build
import           Database.Algebra.Dag.Common
import           Database.DSH.VL.Lang          hiding (DBCol)
import qualified Database.DSH.VL.Lang          as D

--------------------------------------------------------------------------------
-- Construct different types of vectors from algebraic nodes

type VecConst r v = Build VL AlgNode -> Build VL v

dvec :: VecConst r DVec
dvec = fmap (flip DVec [])

pvec :: Build a AlgNode -> Build a PVec
pvec = fmap PVec

rvec :: Build a AlgNode -> Build a RVec
rvec = fmap RVec
     
--------------------------------------------------------------------------------
-- Insert VL operators and appropriate R1/R2/R3 nodes

vec :: VL -> VecConst r a -> Build VL a
vec op mkVec = mkVec $ insertNode op

pairVec :: VL -> VecConst r a -> VecConst r b -> Build VL (a, b)
pairVec op mkVec1 mkVec2 = do
    r <- insertNode op
    r1 <- mkVec1 $ insertNode $ UnOp R1 r
    r2 <- mkVec2 $ insertNode $ UnOp R2 r
    return (r1, r2)

tripleVec :: VL 
          -> VecConst r a 
          -> VecConst r b 
          -> VecConst r c 
          -> Build VL (a, b ,c)
tripleVec op mkVec1 mkVec2 mkVec3 = do
    r <- insertNode op
    r1 <- mkVec1 $ insertNode $ UnOp R1 r
    r2 <- mkVec2 $ insertNode $ UnOp R2 r
    r3 <- mkVec3 $ insertNode $ UnOp R3 r
    return (r1, r2, r3)

--------------------------------------------------------------------------------

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

data ColExpr = Offset Int | Expr Expr

-- | If the child expressions are tuple operators which only give the
-- column offset, convert it into a proper expression first.
offsetExpr :: ColExpr -> Expr
offsetExpr (Offset o) = Column $ o + 1
offsetExpr (Expr e)   = e

addOffset :: Int -> ColExpr -> ColExpr
addOffset _ (Expr _)   = $impossible
addOffset i (Offset o) = Offset $ o + i

toGeneralBinOp :: L.JoinBinOp -> L.ScalarBinOp
toGeneralBinOp (L.JBNumOp o)    = L.SBNumOp o
toGeneralBinOp (L.JBStringOp o) = L.SBStringOp o

toGeneralUnOp :: L.JoinUnOp -> L.ScalarUnOp
toGeneralUnOp (L.JUNumOp o)  = L.SUNumOp o
toGeneralUnOp (L.JUCastOp o) = L.SUCastOp o

toVLjoinConjunct :: L.JoinConjunct L.JoinExpr -> L.JoinConjunct Expr
toVLjoinConjunct (L.JoinConjunct e1 o e2) = 
    L.JoinConjunct (joinExpr e1) o (joinExpr e2)

toVLJoinPred :: L.JoinPredicate L.JoinExpr -> L.JoinPredicate Expr
toVLJoinPred (L.JoinPred cs) = L.JoinPred $ fmap toVLjoinConjunct cs

-- Convert join expressions into VL expressions. The main challenge
-- here is convert sequences of tuple accessors (fst/snd) into VL
-- column indices.
joinExpr :: L.JoinExpr -> Expr
joinExpr expr = offsetExpr $ aux expr
  where
    -- Construct expressions in a bottom-up way. For a given join
    -- expression, return the following:
    -- pair accessors   -> column offset in the flat relational representation
    -- scalar operation -> corresponding VL expression
    aux :: L.JoinExpr -> ColExpr
    -- FIXME VL joins should include join expressions!
    aux (L.JBinOp _ op e1 e2)  = Expr $ BinApp (toGeneralBinOp op)
                                               (offsetExpr $ aux e1)
                                               (offsetExpr $ aux e2)
    aux (L.JUnOp _ op e)       = Expr $ UnApp (toGeneralUnOp op) (offsetExpr $ aux e)
    aux (L.JFst _ e)           = aux e
    aux (L.JSnd _ e)           =
        case Ty.typeOf e of
            Ty.PairT t1 _ -> addOffset (recordWidth t1) (aux e)
            _             -> $impossible
    aux (L.JLit _ v)           = Expr $ Constant $ pVal v
    aux (L.JInput _)           = Offset 0


----------------------------------------------------------------------------------
-- DAG constructor functions for VL operators

vlUniqueS :: DVec -> Build VL DVec
vlUniqueS (DVec c _) = vec (UnOp UniqueS c) dvec

vlNumber :: DVec -> Build VL DVec
vlNumber (DVec c _) = vec (UnOp Number c) dvec

vlNumberS :: DVec -> Build VL DVec
vlNumberS (DVec c _) = vec (UnOp NumberS c) dvec

vlGroupBy :: DVec -> DVec -> Build VL (DVec, DVec, PVec)
vlGroupBy (DVec c1 _) (DVec c2 _) = tripleVec (BinOp GroupBy c1 c2) dvec dvec pvec

vlSort :: DVec -> DVec -> Build VL (DVec, PVec)
vlSort (DVec c1 _) (DVec c2 _) = pairVec (BinOp SortS c1 c2) dvec pvec

vlAggr :: AggrFun -> DVec -> Build VL DVec
vlAggr aFun (DVec c _) = vec (UnOp (Aggr aFun) c) dvec

vlAggrS :: AggrFun -> DVec -> DVec -> Build VL DVec
vlAggrS aFun (DVec c1 _) (DVec c2 _) = vec (BinOp (AggrS aFun) c1 c2) dvec

vlDescToRename :: DVec -> Build VL RVec
vlDescToRename (DVec c _) = vec (UnOp DescToRename c) rvec

vlDistPrim :: DVec -> DVec -> Build VL (DVec, PVec)
vlDistPrim (DVec c1 _) (DVec c2 _) = pairVec (BinOp DistPrim c1 c2) dvec pvec

vlDistDesc :: DVec -> DVec -> Build VL (DVec, PVec)
vlDistDesc (DVec c1 _) (DVec c2 _) = pairVec (BinOp DistDesc c1 c2) dvec pvec

vlAlign :: DVec -> DVec -> Build VL (DVec, PVec)
vlAlign (DVec c1 _) (DVec c2 _) = pairVec (BinOp Align c1 c2) dvec pvec

vlPropRename :: RVec -> DVec -> Build VL DVec
vlPropRename (RVec c1) (DVec c2 _) = vec (BinOp PropRename c1 c2) dvec

vlUnbox :: RVec -> DVec -> Build VL (DVec, RVec)
vlUnbox (RVec c1) (DVec c2 _) = pairVec (BinOp Unbox c1 c2) dvec rvec

vlPropFilter :: RVec -> DVec -> Build VL (DVec, RVec)
vlPropFilter (RVec c1) (DVec c2 _) = pairVec (BinOp PropFilter c1 c2) dvec rvec

vlPropReorder :: PVec -> DVec -> Build VL (DVec, PVec)
vlPropReorder (PVec c1) (DVec c2 _) = pairVec (BinOp PropReorder c1 c2) dvec pvec

vlSingletonDescr :: Build VL DVec
vlSingletonDescr = vec (NullaryOp SingletonDescr) dvec

vlAppend :: DVec -> DVec -> Build VL (DVec, RVec, RVec)
vlAppend (DVec c1 _) (DVec c2 _) = tripleVec (BinOp Append c1 c2) dvec rvec rvec

vlAppendS :: DVec -> DVec -> Build VL (DVec, RVec, RVec)
vlAppendS (DVec c1 _) (DVec c2 _) = tripleVec (BinOp AppendS c1 c2) dvec rvec rvec

vlSegment :: DVec -> Build VL DVec
vlSegment (DVec c _) = vec (UnOp Segment c) dvec

vlUnsegment :: DVec -> Build VL DVec
vlUnsegment (DVec c _) = vec (UnOp Unsegment c) dvec

vlRestrict :: DVec -> DVec -> Build VL (DVec, RVec)
vlRestrict (DVec c1 _) (DVec c2 _) = pairVec (BinOp Restrict c1 c2) dvec rvec

vlCombine :: DVec -> DVec -> DVec -> Build VL (DVec, RVec, RVec)
vlCombine (DVec c1 _) (DVec c2 _) (DVec c3 _) = 
    tripleVec (TerOp Combine c1 c2 c3) dvec rvec rvec

vlLit :: L.Emptiness -> [Ty.Type] -> [[VLVal]] -> Build VL DVec
vlLit em tys vals = vec (NullaryOp $ Lit em (map typeToVLType tys) vals) dvec

vlTableRef :: String -> [VLColumn] -> L.TableHints -> Build VL DVec
vlTableRef n tys hs = vec (NullaryOp $ TableRef n tys hs) dvec

vlUnExpr :: L.ScalarUnOp -> DVec -> Build VL DVec
vlUnExpr o (DVec c _) = vec (UnOp (Project [UnApp o (Column 1)]) c) dvec

vlBinExpr :: L.ScalarBinOp -> DVec -> DVec -> Build VL DVec
vlBinExpr o (DVec c1 _) (DVec c2 _) = do
    z <- insertNode $ BinOp Zip c1 c2
    r <- dvec $ insertNode $ UnOp (Project [BinApp o (Column 1) (Column 2)]) z
    return r

vlSelectPos :: DVec -> L.ScalarBinOp -> DVec -> Build VL (DVec, RVec, RVec)
vlSelectPos (DVec c1 _) op (DVec c2 _) = tripleVec (BinOp (SelectPos op) c1 c2) dvec rvec rvec

vlSelectPos1 :: DVec -> L.ScalarBinOp -> Nat -> Build VL (DVec, RVec, RVec)
vlSelectPos1 (DVec c1 _) op posConst = 
    tripleVec (UnOp (SelectPos1 op posConst) c1) dvec rvec rvec

vlSelectPosS :: DVec -> L.ScalarBinOp -> DVec -> Build VL (DVec, RVec, RVec)
vlSelectPosS (DVec c1 _) op (DVec c2 _) = do
    tripleVec (BinOp (SelectPosS op) c1 c2) dvec rvec rvec

vlSelectPos1S :: DVec -> L.ScalarBinOp -> Nat -> Build VL (DVec, RVec, RVec)
vlSelectPos1S (DVec c1 _) op posConst = 
    tripleVec (UnOp (SelectPos1S op posConst) c1) dvec rvec rvec

vlProject :: DVec -> [Expr] -> Build VL DVec
vlProject (DVec c _) projs = dvec $ insertNode $ UnOp (Project projs) c

vlZip :: DVec -> DVec -> Build VL DVec
vlZip (DVec c1 _) (DVec c2 _) = vec (BinOp Zip c1 c2) dvec

vlZipS :: DVec -> DVec -> Build VL (DVec, RVec, RVec)
vlZipS (DVec c1 _) (DVec c2 _) =
    tripleVec (BinOp ZipS c1 c2) dvec rvec rvec

vlCartProduct :: DVec -> DVec -> Build VL (DVec, PVec, PVec)
vlCartProduct (DVec c1 _) (DVec c2 _) =
    tripleVec (BinOp CartProduct c1 c2) dvec pvec pvec

vlCartProductS :: DVec -> DVec -> Build VL (DVec, PVec, PVec)
vlCartProductS (DVec c1 _) (DVec c2 _) =
    tripleVec (BinOp CartProductS c1 c2) dvec pvec pvec

vlThetaJoin :: L.JoinPredicate L.JoinExpr -> DVec -> DVec -> Build VL (DVec, PVec, PVec)
vlThetaJoin joinPred (DVec c1 _) (DVec c2 _) =
    tripleVec (BinOp (ThetaJoin joinPred') c1 c2) dvec pvec pvec
  where
    joinPred' = toVLJoinPred joinPred

vlThetaJoinS :: L.JoinPredicate L.JoinExpr -> DVec -> DVec -> Build VL (DVec, PVec, PVec)
vlThetaJoinS joinPred (DVec c1 _) (DVec c2 _) =
    tripleVec (BinOp (ThetaJoinS joinPred') c1 c2) dvec pvec pvec
  where
    joinPred' = toVLJoinPred joinPred

vlNestJoinS :: L.JoinPredicate L.JoinExpr -> DVec -> DVec -> Build VL (DVec, PVec)
vlNestJoinS joinPred (DVec c1 _) (DVec c2 _) =
    pairVec (BinOp (NestJoinS joinPred') c1 c2) dvec pvec
  where
    joinPred' = toVLJoinPred joinPred

vlNestProductS :: DVec -> DVec -> Build VL (DVec, PVec)
vlNestProductS (DVec c1 _) (DVec c2 _) = do
    pairVec (BinOp NestProductS c1 c2) dvec pvec

vlSemiJoin :: L.JoinPredicate L.JoinExpr -> DVec -> DVec -> Build VL (DVec, RVec)
vlSemiJoin joinPred (DVec c1 _) (DVec c2 _) = do
    pairVec (BinOp (SemiJoin joinPred') c1 c2) dvec rvec
  where
    joinPred' = toVLJoinPred joinPred

vlSemiJoinS :: L.JoinPredicate L.JoinExpr -> DVec -> DVec -> Build VL (DVec, RVec)
vlSemiJoinS joinPred (DVec c1 _) (DVec c2 _) = do
    pairVec (BinOp (SemiJoinS joinPred') c1 c2) dvec rvec
  where
    joinPred' = toVLJoinPred joinPred

vlAntiJoin :: L.JoinPredicate L.JoinExpr -> DVec -> DVec -> Build VL (DVec, RVec)
vlAntiJoin joinPred (DVec c1 _) (DVec c2 _) = do
    pairVec (BinOp (AntiJoin joinPred') c1 c2) dvec rvec
  where
    joinPred' = toVLJoinPred joinPred

vlAntiJoinS :: L.JoinPredicate L.JoinExpr -> DVec -> DVec -> Build VL (DVec, RVec)
vlAntiJoinS joinPred (DVec c1 _) (DVec c2 _) = do
    pairVec (BinOp (AntiJoinS joinPred') c1 c2) dvec rvec
  where
    joinPred' = toVLJoinPred joinPred

vlReverse :: DVec -> Build VL (DVec, PVec)
vlReverse (DVec c _) = pairVec (UnOp Reverse c) dvec pvec

vlReverseS :: DVec -> Build VL (DVec, PVec)
vlReverseS (DVec c _) = pairVec (UnOp ReverseS c) dvec pvec

vlTranspose :: DVec -> Build VL (DVec, DVec)
vlTranspose (DVec c _) = pairVec (UnOp Transpose c) dvec dvec

vlTransposeS :: DVec -> DVec -> Build VL (DVec, DVec)
vlTransposeS (DVec c1 _) (DVec c2 _) = do
    pairVec (BinOp TransposeS c1 c2) dvec dvec

vlReshape :: Integer -> DVec -> Build VL (DVec, DVec)
vlReshape n (DVec c _) = do
    pairVec (UnOp (Reshape n) c) dvec dvec

vlReshapeS :: Integer -> DVec -> Build VL (DVec, DVec)
vlReshapeS n (DVec c _) = do
    pairVec (UnOp (ReshapeS n) c) dvec dvec
