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
import           Database.DSH.VL.Shape            hiding (Pair)
import           Database.DSH.VL.VectorOperations
import           Database.DSH.VL.VLPrimitives

--------------------------------------------------------------------------------
-- Extend the DAG builder monad with an environment for compiled VL
-- DAGs.

type Env = [(String, Shape)]

type EnvBuild = ReaderT Env (Build VL.VL)

-- FIXME might need those when let-expressions have been introduced.
lookupEnv :: String -> EnvBuild Shape
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

fkl2VL :: Expr -> EnvBuild Shape
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
        PApp3 _ (Combine _) arg1 arg2 arg3 -> do
            arg1' <- fkl2VL arg1
            arg2' <- fkl2VL arg2
            arg3' <- fkl2VL arg3
            lift $ combine arg1' arg2' arg3'
        Var _ s -> lookupEnv s

papp1 :: Type -> Prim1 -> Shape -> Build VL.VL Shape
papp1 t f =
    case f of
        Length _           -> lengthV
-- FIXME what is wrong here?
--        FLengthL _          -> lengthLift
        LengthL _          -> $impossible
        ConcatL _          -> concatLift
        Sum _              -> aggrPrim $ VL.AggrSum $ typeToRowType t
        SumL _             -> aggrLift $ VL.AggrSum $ typeToRowType $ elemT t
        Avg _              -> aggrPrim VL.AggrAvg
        AvgL _             -> aggrLift VL.AggrAvg
        The _              -> the
        TheL _             -> theL
        Fst _              -> fstA
        Snd _              -> sndA
        FstL _             -> fstL
        SndL _             -> sndL
        Concat _           -> concatV
        QuickConcat _      -> quickConcatV
        Minimum _          -> aggrPrim VL.AggrMin
        MinimumL _         -> aggrLift VL.AggrMin
        Maximum _          -> aggrPrim VL.AggrMax
        MaximumL _         -> aggrLift VL.AggrMax
        Tail _             -> tailS
        TailL _            -> tailL
        Reverse _          -> reversePrim
        ReverseL _         -> reverseLift
        And _              -> aggrPrim VL.AggrAll
        AndL _             -> aggrLift VL.AggrAll
        Or _               -> aggrPrim VL.AggrAny
        OrL _              -> aggrLift VL.AggrAny
        Init _             -> initPrim
        InitL _            -> initLift
        Last _             -> lastPrim
        LastL _            -> lastLift
        Nub _              -> nubPrim
        NubL _             -> nubLift
        Number _           -> numberPrim
        NumberL _          -> numberLift
        Transpose _        -> transposePrim
        TransposeL _       -> transposeLift
        Reshape n _        -> reshapePrim n
        ReshapeL n _       -> reshapeLift n

papp2 :: Prim2 -> Shape -> Shape -> Build VL.VL Shape
papp2 f =
    case f of
        Dist _            -> dist
        DistL _           -> distL
        Group _           -> groupByKeyS
        GroupL _          -> groupByKeyL
        Sort _            -> sortWithS
        SortL _           -> sortWithL
        Restrict _        -> restrict
        RestrictL _       -> $unimplemented
        Unconcat _        -> unconcatV
        Pair _            -> pairOp
        PairL _           -> pairOpL
        Append _          -> appendPrim
        AppendL _         -> appendLift
        Index _           -> indexPrim
        IndexL _          -> indexLift
        Zip _             -> zipPrim
        ZipL _            -> zipLift
        Cons _            -> cons
        ConsL _           -> consLift
        CartProduct _     -> cartProductPrim
        CartProductL _    -> cartProductLift
        NestProduct _     -> nestProductPrim
        NestProductL _    -> nestProductLift
        ThetaJoin p _     -> thetaJoinPrim p
        ThetaJoinL p _    -> thetaJoinLift p
        NestJoin p _      -> nestJoinPrim p
        NestJoinL p _     -> nestJoinLift p
        SemiJoin p _      -> semiJoinPrim p
        SemiJoinL p _     -> semiJoinLift p
        AntiJoin p _      -> antiJoinPrim p
        AntiJoinL p _     -> antiJoinLift p

-- For each top node, determine the number of columns the vector has and insert
-- a dummy projection which just copies those columns. This is to ensure that
-- columns which are required from the top are not pruned by optimizations.
insertTopProjections :: Build VL.VL Shape -> Build VL.VL (QP.TopShape VLDVec)
insertTopProjections g = do
    shape <- g
    let shape' = QP.exportShape shape
    traverseShape shape'

  where
    traverseShape :: (QP.TopShape VLDVec) -> Build VL.VL (QP.TopShape VLDVec)
    traverseShape (QP.ValueVector (VLDVec q) lyt) =
        insertProj lyt q VL.Project VLDVec QP.ValueVector
    traverseShape (QP.PrimVal (VLDVec q) lyt)     =
        insertProj lyt q VL.Project VLDVec QP.PrimVal
  
    traverseLayout :: (QP.TopLayout VLDVec) -> Build VL.VL (QP.TopLayout VLDVec)
    traverseLayout (QP.InColumn c) =
        return $ QP.InColumn c
    traverseLayout (QP.Pair lyt1 lyt2) = do
        lyt1' <- traverseLayout lyt1
        lyt2' <- traverseLayout lyt2
        return $ QP.Pair lyt1' lyt2'
    traverseLayout (QP.Nest (VLDVec q) lyt) =
      insertProj lyt q VL.Project VLDVec QP.Nest

    insertProj
      :: QP.TopLayout VLDVec               -- ^ The node's layout
      -> Alg.AlgNode                       -- ^ The top node to consider
      -> ([VL.Expr] -> VL.UnOp)            -- ^ Constructor for the projection op
      -> (Alg.AlgNode -> v)                -- ^ Vector constructor
      -> (v -> (QP.TopLayout VLDVec) -> t) -- ^ Layout/Shape constructor
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
