{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections   #-}

module Database.DSH.Translate.FKL2VL (specializeVectorOps) where

import Debug.Trace

import           Control.Monad
import           Control.Monad.Reader

import           Database.Algebra.Dag.Build
import qualified Database.Algebra.Dag.Common      as Alg

import           Database.DSH.Common.Pretty
import qualified Database.DSH.Common.QueryPlan    as QP
import           Database.DSH.Common.Type
import           Database.DSH.FKL.Lang
import           Database.DSH.FKL.Pretty()
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

{-

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

fkl2VL :: Expr -> EnvBuild (Shape VLDVec)
fkl2VL expr =
    case expr of
        Table _ n cs hs -> lift $ dbTable n cs hs
        Const t v -> lift $ mkLiteral t v
        BinOp _ (NotLifted o) e1 e2    -> do
            PrimVal p1 lyt <- fkl2VL e1
            PrimVal p2 _   <- fkl2VL e2
            p              <- lift $ vlBinExpr o p1 p2
            return $ PrimVal p lyt
        BinOp _ (Lifted o) e1 e2     -> do
            ValueVector p1 lyt <- fkl2VL e1
            ValueVector p2 _   <- fkl2VL e2
            p                  <- lift $ vlBinExpr o p1 p2
            return $ ValueVector p lyt
        UnOp _ (NotLifted o) e1 -> do
            PrimVal p1 lyt <- fkl2VL e1
            p              <- lift $ vlUnExpr o p1
            return $ PrimVal p lyt
        UnOp _ (Lifted o) e1 -> do
            ValueVector p1 lyt <- fkl2VL e1
            p                  <- lift $ vlUnExpr o p1
            return $ ValueVector p lyt
        If _ eb e1 e2 -> do
            eb' <- fkl2VL eb
            e1' <- fkl2VL e1
            e2' <- fkl2VL e2
            lift $ ifList eb' e1' e2'
        PApp1 t f arg -> do
            arg' <- fkl2VL arg
            lift $ papp1 t f arg'
        PApp2 _ f arg1 arg2 -> do
            arg1' <- fkl2VL arg1
            arg2' <- fkl2VL arg2
            lift $ papp2 f arg1' arg2'
        PApp3 _ Combine arg1 arg2 arg3 -> do
            arg1' <- fkl2VL arg1
            arg2' <- fkl2VL arg2
            arg3' <- fkl2VL arg3
            lift $ combine arg1' arg2' arg3'
        Var _ s -> lookupEnv s

papp1 :: Type -> Prim1 -> Shape VLDVec -> Build VL.VL (Shape VLDVec)
papp1 t f =
    case f of
        Length           -> lengthV
-- FIXME what is wrong here?
--        FLengthL          -> lengthLift
        LengthL          -> $impossible
        ConcatL          -> concatLift
        Sum              -> aggrPrim $ VL.AggrSum $ typeToRowType t
        SumL             -> aggrLift $ VL.AggrSum $ typeToRowType $ elemT t
        Avg              -> aggrPrim VL.AggrAvg
        AvgL             -> aggrLift VL.AggrAvg
        The              -> the
        TheL             -> theL
        Fst              -> fstA
        Snd              -> sndA
        FstL             -> fstL
        SndL             -> sndL
        Concat           -> concatV
        QuickConcat      -> quickConcatV
        Minimum          -> aggrPrim VL.AggrMin
        MinimumL         -> aggrLift VL.AggrMin
        Maximum          -> aggrPrim VL.AggrMax
        MaximumL         -> aggrLift VL.AggrMax
        Tail             -> tailS
        TailL            -> tailL
        Reverse          -> reversePrim
        ReverseL         -> reverseLift
        And              -> aggrPrim VL.AggrAll
        AndL             -> aggrLift VL.AggrAll
        Or               -> aggrPrim VL.AggrAny
        OrL              -> aggrLift VL.AggrAny
        Init             -> initPrim
        InitL            -> initLift
        Last             -> lastPrim
        LastL            -> lastLift
        Nub              -> nubPrim
        NubL             -> nubLift
        Number           -> numberPrim
        NumberL          -> numberLift
        Transpose        -> transposePrim
        TransposeL       -> transposeLift
        Reshape n        -> reshapePrim n
        ReshapeL n       -> reshapeLift n

papp2 :: Prim2 -> Shape VLDVec -> Shape VLDVec -> Build VL.VL (Shape VLDVec)
papp2 f =
    case f of
        Dist            -> dist
        DistL           -> distL
        Group           -> groupByKeyS
        GroupL          -> groupByKeyL
        Sort            -> sortWithS
        SortL           -> sortWithL
        Restrict        -> restrict
        RestrictL       -> $unimplemented
        Unconcat        -> unconcatV
        Pair            -> pairOp
        PairL           -> pairOpL
        Append          -> appendPrim
        AppendL         -> appendLift
        Index           -> indexPrim
        IndexL          -> indexLift
        Zip             -> zipPrim
        ZipL            -> zipLift
        Cons            -> cons
        ConsL           -> consLift
        CartProduct     -> cartProductPrim
        CartProductL    -> cartProductLift
        NestProduct     -> nestProductPrim
        NestProductL    -> nestProductLift
        ThetaJoin p     -> thetaJoinPrim p
        ThetaJoinL p    -> thetaJoinLift p
        NestJoin p      -> nestJoinPrim p
        NestJoinL p     -> nestJoinLift p
        SemiJoin p      -> semiJoinPrim p
        SemiJoinL p     -> semiJoinLift p
        AntiJoin p      -> antiJoinPrim p
        AntiJoinL p     -> antiJoinLift p

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
specializeVectorOps e = trace (pp e) $ QP.mkQueryPlan opMap shape tagMap
  where
    (opMap, shape, tagMap) = runBuild (insertTopProjections $ runReaderT (fkl2VL e) [])

-}

specializeVectorOps = $unimplemented
