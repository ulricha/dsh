{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections   #-}

module Database.DSH.Translate.FKL2VL (specializeVectorOps) where

import           Control.Monad.Reader

import           Database.Algebra.Dag.Build
import qualified Database.Algebra.Dag.Common      as Alg

import           Database.DSH.Common.Pretty
import qualified Database.DSH.Common.QueryPlan    as QP
import           Database.DSH.Common.Type
import           Database.DSH.FKL.Lang
import           Database.DSH.Impossible
import           Database.DSH.VL.Vector
import qualified Database.DSH.VL.Lang             as VL
import           Database.DSH.VL.Render.JSON      ()
import           Database.DSH.Common.QueryPlan    hiding (Pair)
import           Database.DSH.VL.VectorOperations
import           Database.DSH.VL.VLPrimitives

--------------------------------------------------------------------------------
-- Extend the DAG builder monad with an environment for compiled VL
-- DAGs.

type Env = [(String, Shape VLDVec)]

type EnvBuild = ReaderT Env (Build VL.VL)

-- FIXME might need those when let-expressions have been introduced.
lookupEnv :: String -> EnvBuild (Shape VLDVec)
lookupEnv n = ask >>= \env -> case lookup n env of
    Just r -> return r
    Nothing -> $impossible

{-
withEnv :: Env -> EnvBuild a -> EnvBuild a
withEnv env = local (const env)
-}

{-
-- | Evaluate the graph construction computation with a different
-- environment. Return within the current computational context.
withEnv :: Gam a -> AlgNode -> Build a alg r -> Build a alg r
withEnv gam loop = local (\_ -> (gam, loop))
-}

--------------------------------------------------------------------------------
-- Compilation from FKL expressions to a VL DAG.

fkl2VL :: Expr -> Build VL.VL (Shape VLDVec)
fkl2VL expr =
    case expr of
        Table _ n cs hs -> dbTable n cs hs
        Const t v -> mkLiteral t v
        BinOp _ (NotLifted o) e1 e2    -> do
            PrimVal p1 lyt <- fkl2VL e1
            PrimVal p2 _   <- fkl2VL e2
            p              <-  vlBinExpr o p1 p2
            return $ PrimVal p lyt
        BinOp _ (Lifted o) e1 e2     -> do
            ValueVector p1 lyt <- fkl2VL e1
            ValueVector p2 _   <- fkl2VL e2
            p                  <-  vlBinExpr o p1 p2
            return $ ValueVector p lyt
        UnOp _ (NotLifted o) e1 -> do
            PrimVal p1 lyt <- fkl2VL e1
            p              <-  vlUnExpr o p1
            return $ PrimVal p lyt
        UnOp _ (Lifted o) e1 -> do
            ValueVector p1 lyt <- fkl2VL e1
            p                  <-  vlUnExpr o p1
            return $ ValueVector p lyt
        If _ eb e1 e2 -> do
            eb' <- fkl2VL eb
            e1' <- fkl2VL e1
            e2' <- fkl2VL e2
            ifList eb' e1' e2'
        PApp1 t f arg -> do
            arg' <- fkl2VL arg
            papp1 t f arg'
        PApp2 _ f arg1 arg2 -> do
            arg1' <- fkl2VL arg1
            arg2' <- fkl2VL arg2
            papp2 f arg1' arg2'
        PApp3 _ p arg1 arg2 arg3 -> do
            arg1' <- fkl2VL arg1
            arg2' <- fkl2VL arg2
            arg3' <- fkl2VL arg3
            papp3 p arg1' arg2' arg3'
        QConcat n _ arg -> do
            arg <- fkl2VL arg
            return $ qConcatV n arg
        UnConcat n _ arg1 arg2 -> do
            arg1' <- fkl2VL arg1
            arg2' <- fkl2VL arg2
            return $ unconcatN n arg1' arg2'
             

papp3 :: Lifted Prim3 -> Shape VLDVec -> Shape VLDVec -> Shape VLDVec -> Build VL.VL (Shape VLDVec)
papp3 (Lifted Combine)    = $unimplemented
papp3 (NotLifted Combine) = combine 

papp1 :: Type -> Lifted Prim1 -> Shape VLDVec -> Build VL.VL (Shape VLDVec)
papp1 t (Lifted f) =
    case f of
-- FIXME what is wrong here?
--        FLengthL          -> lengthLift
        Length          -> $impossible
        Concat          -> concatLift
        Sum             -> aggrLift $ VL.AggrSum $ typeToRowType $ elemT t
        Avg             -> aggrLift VL.AggrAvg
        The             -> theL
        Fst             -> fstL
        Snd             -> sndL
        Minimum         -> aggrLift VL.AggrMin
        Maximum         -> aggrLift VL.AggrMax
        Tail            -> tailL
        Reverse         -> reverseLift
        And             -> aggrLift VL.AggrAll
        Or              -> aggrLift VL.AggrAny
        Init            -> initLift
        Last            -> lastLift
        Nub             -> nubLift
        Number          -> numberLift
        Transpose       -> transposeLift
        Reshape n       -> reshapeLift n

papp1 t (NotLifted f) =
    case f of
        Length          -> lengthV
        Sum              -> aggrPrim $ VL.AggrSum $ typeToRowType t
        Avg              -> aggrPrim VL.AggrAvg
        Reshape n        -> reshapePrim n
        Transpose        -> transposePrim
        Number           -> numberPrim
        Nub              -> nubPrim
        Last             -> lastPrim
        Init             -> initPrim
        Or               -> aggrPrim VL.AggrAny
        And              -> aggrPrim VL.AggrAll
        Reverse          -> reversePrim
        Tail             -> tailS
        Maximum          -> aggrPrim VL.AggrMax
        Minimum          -> aggrPrim VL.AggrMin
        Concat           -> concatV
        -- QuickConcat      -> quickConcatV
        Fst              -> fstA
        Snd              -> sndA
        The              -> the

papp2 :: Lifted Prim2 -> Shape VLDVec -> Shape VLDVec -> Build VL.VL (Shape VLDVec)
papp2 (Lifted f) =
    case f of
        Dist           -> distL
        Group          -> groupByKeyL
        Sort           -> sortWithL
        Restrict       -> $unimplemented
        Pair           -> pairOpL
        Append         -> appendLift
        Index          -> indexLift
        Zip            -> zipLift
        Cons           -> consLift
        CartProduct    -> cartProductLift
        NestProduct    -> nestProductLift
        ThetaJoin p    -> thetaJoinLift p
        NestJoin p     -> nestJoinLift p
        SemiJoin p     -> semiJoinLift p
        AntiJoin p     -> antiJoinLift p

papp2 (NotLifted f) =
    case f of
        Dist            -> dist
        Group           -> groupByKeyS
        Sort            -> sortWithS
        Restrict        -> restrict
        -- Unconcat        -> unconcatV
        Pair            -> pairOp
        Append          -> appendPrim
        Index           -> indexPrim
        Zip             -> zipPrim
        Cons            -> cons
        CartProduct     -> cartProductPrim
        NestProduct     -> nestProductPrim
        ThetaJoin p     -> thetaJoinPrim p
        NestJoin p      -> nestJoinPrim p
        SemiJoin p      -> semiJoinPrim p
        AntiJoin p      -> antiJoinPrim p

-- For each top node, determine the number of columns the vector has and insert
-- a dummy projection which just copies those columns. This is to ensure that
-- columns which are required from the top are not pruned by optimizations.
insertTopProjections :: Build VL.VL (QP.Shape VLDVec) -> Build VL.VL (QP.Shape VLDVec)
insertTopProjections g = g >>= traverseShape

  where
    traverseShape :: QP.Shape VLDVec -> Build VL.VL (QP.Shape VLDVec)
    traverseShape (QP.ValueVector (VLDVec q) lyt) =
        insertProj lyt q VL.Project VLDVec QP.ValueVector
    traverseShape (QP.PrimVal (VLDVec q) lyt)     =
        insertProj lyt q VL.Project VLDVec QP.PrimVal
  
    traverseLayout :: (QP.Layout VLDVec) -> Build VL.VL (QP.Layout VLDVec)
    traverseLayout (QP.InColumn c) =
        return $ QP.InColumn c
    traverseLayout (QP.Pair lyt1 lyt2) = do
        lyt1' <- traverseLayout lyt1
        lyt2' <- traverseLayout lyt2
        return $ QP.Pair lyt1' lyt2'
    traverseLayout (QP.Nest (VLDVec q) lyt) =
      insertProj lyt q VL.Project VLDVec QP.Nest

    insertProj
      :: QP.Layout VLDVec               -- ^ The node's layout
      -> Alg.AlgNode                    -- ^ The top node to consider
      -> ([VL.Expr] -> VL.UnOp)         -- ^ Constructor for the projection op
      -> (Alg.AlgNode -> v)             -- ^ Vector constructor
      -> (v -> (QP.Layout VLDVec) -> t) -- ^ Layout/Shape constructor
      -> Build VL.VL t
    insertProj lyt q project vector describe = do
        let width = QP.columnsInLayout lyt
            cols  = [1 .. width]
        qp   <- insertNode $ Alg.UnOp (project $ map VL.Column cols) q
        lyt' <- traverseLayout lyt
        return $ describe (vector qp) lyt'

-- | Compile a FKL expression into a query plan of vector operators (VL)
specializeVectorOps :: Expr -> QP.QueryPlan VL.VL VLDVec
specializeVectorOps e = QP.mkQueryPlan opMap shape tagMap
  where
    (opMap, shape, tagMap) = runBuild (insertTopProjections $ fkl2VL e)
