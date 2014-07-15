{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections   #-}

module Database.DSH.Translate.FKL2VL (specializeVectorOps) where

import           Control.Monad
import           Control.Monad.Reader

import           Database.Algebra.Dag.Build
import qualified Database.Algebra.Dag.Common      as Alg

import qualified Database.DSH.Common.QueryPlan    as QP
import           Database.DSH.Common.Type
import           Database.DSH.FKL.Data.FKL
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

lookupEnv :: String -> EnvBuild Shape
lookupEnv n = ask >>= \env -> case lookup n env of
    Just r -> return r
    Nothing -> $impossible

withEnv :: Env -> EnvBuild a -> EnvBuild a
withEnv env = local (const env)

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
        PApp3 _ (FCombine _) arg1 arg2 arg3 -> do
            arg1' <- fkl2VL arg1
            arg2' <- fkl2VL arg2
            arg3' <- fkl2VL arg3
            lift $ combine arg1' arg2' arg3'
        Var _ s -> lookupEnv s
        Clo _ n fvs x f1 f2 -> do
            fv <- constructClosureEnv fvs
            return $ Closure n fv x f1 f2
        AClo _ n fvs x f1 f2 -> do
            v  <- lookupEnv n
            fv <- constructClosureEnv fvs
            return $ AClosure n v 1 fv x f1 f2
        CloApp _ c arg -> do
            Closure _ fvs x f1 _ <- fkl2VL c
            arg'                 <- fkl2VL arg
            withEnv ((x, arg'):fvs) $ fkl2VL f1
        CloLApp _ c arg -> do
            AClosure n v 1 fvs x _ f2 <- fkl2VL c
            arg'                      <- fkl2VL arg
            withEnv ((n, v):(x, arg'):fvs) $ fkl2VL f2

papp1 :: Type -> Prim1 -> Shape -> Build VL.VL Shape
papp1 t f =
    case f of
        FLength _           -> lengthV
        FLengthL _          -> lengthLift
        FConcatL _          -> concatLift
        FSum _              -> aggrPrim $ VL.AggrSum $ typeToRowType t
        FSumL _             -> aggrLift $ VL.AggrSum $ typeToRowType $ elemT t
        FAvg _              -> aggrPrim VL.AggrAvg
        FAvgL _             -> aggrLift VL.AggrAvg
        FThe _              -> the
        FTheL _             -> theL
        FFst _              -> fstA
        FSnd _              -> sndA
        FFstL _             -> fstL
        FSndL _             -> sndL
        FConcat _           -> concatV
        FQuickConcat _      -> quickConcatV
        FMinimum _          -> aggrPrim VL.AggrMin
        FMinimumL _         -> aggrLift VL.AggrMin
        FMaximum _          -> aggrPrim VL.AggrMax
        FMaximumL _         -> aggrLift VL.AggrMax
        FTail _             -> tailS
        FTailL _            -> tailL
        FReverse _          -> reversePrim
        FReverseL _         -> reverseLift
        FAnd _              -> aggrPrim VL.AggrAll
        FAndL _             -> aggrLift VL.AggrAll
        FOr _               -> aggrPrim VL.AggrAny
        FOrL _              -> aggrLift VL.AggrAny
        FInit _             -> initPrim
        FInitL _            -> initLift
        FLast _             -> lastPrim
        FLastL _            -> lastLift
        FNub _              -> nubPrim
        FNubL _             -> nubLift
        FNumber _           -> numberPrim
        FNumberL _          -> numberLift
        FTranspose _        -> transposePrim
        FTransposeL _       -> transposeLift
        FReshape n _        -> reshapePrim n
        FReshapeL n _       -> reshapeLift n

papp2 :: Prim2 -> Shape -> Shape -> Build VL.VL Shape
papp2 f =
    case f of
        FDist _            -> dist
        FDistL _           -> distL
        FGroupWithKey _    -> groupByKeyS
        FGroupWithKeyL _   -> groupByKeyL
        FSortWithS _       -> sortWithS
        FSortWithL _       -> sortWithL
        FRestrict _        -> restrict
        FUnconcat _        -> unconcatV
        FPair _            -> pairOp
        FPairL _           -> pairOpL
        FAppend _          -> appendPrim
        FAppendL _         -> appendLift
        FIndex _           -> indexPrim
        FIndexL _          -> indexLift
        FZip _             -> zipPrim
        FZipL _            -> zipLift
        FCons _            -> cons
        FConsL _           -> consLift
        FCartProduct _     -> cartProductPrim
        FCartProductL _    -> cartProductLift
        FNestProduct _     -> nestProductPrim
        FNestProductL _    -> nestProductLift
        FThetaJoin p _     -> thetaJoinPrim p
        FThetaJoinL p _    -> thetaJoinLift p
        FNestJoin p _      -> nestJoinPrim p
        FNestJoinL p _     -> nestJoinLift p
        FSemiJoin p _      -> semiJoinPrim p
        FSemiJoinL p _     -> semiJoinLift p
        FAntiJoin p _      -> antiJoinPrim p
        FAntiJoinL p _     -> antiJoinLift p

constructClosureEnv :: [String] -> EnvBuild Env
constructClosureEnv []     = return []
constructClosureEnv (x:xs) = liftM2 (:) (liftM (x,) $ lookupEnv x) (constructClosureEnv xs)

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
specializeVectorOps e = QP.mkQueryPlan opMap shape tagMap
  where
    (opMap, shape, tagMap) = runBuild (insertTopProjections $ runReaderT (fkl2VL e) [])
