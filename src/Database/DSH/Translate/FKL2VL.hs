{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections   #-}

module Database.DSH.Translate.FKL2VL (specializeVectorOps) where

import           Debug.Trace

import           Control.Monad.Reader


import           Database.Algebra.Dag.Build
import qualified Database.Algebra.Dag.Common   as Alg

import           Database.DSH.Common.Lang
import           Database.DSH.Common.Pretty
import           Database.DSH.Common.QueryPlan
import           Database.DSH.Common.Type
import           Database.DSH.FKL.Lang
import           Database.DSH.Impossible
import qualified Database.DSH.VL.Lang          as VL
import           Database.DSH.VL.Render.JSON   ()
import           Database.DSH.VL.Vector
import qualified Database.DSH.VL.Vectorize     as V
import           Database.DSH.VL.Primitives

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

bind :: Ident -> Shape VLDVec -> Env -> Env
bind n e env = (n, e) : env

--------------------------------------------------------------------------------
-- Compilation from FKL expressions to a VL DAG.

fkl2VL :: FExpr -> EnvBuild (Shape VLDVec)
fkl2VL expr =
    case expr of
        Var _ n -> lookupEnv n
        Let _ n e1 e -> do
            e1' <- fkl2VL e1
            local (bind n e1') $ fkl2VL e
        Table _ n cs hs -> lift $ V.dbTable n cs hs
        Const t v -> lift $ V.mkLiteral t v
        BinOp _ (NotLifted o) e1 e2    -> do
            SShape p1 lyt <- fkl2VL e1
            SShape p2 _   <- fkl2VL e2
            p              <- lift $ vlBinExpr o p1 p2
            return $ SShape p lyt
        BinOp _ (Lifted o) e1 e2     -> do
            VShape p1 lyt <- fkl2VL e1
            VShape p2 _   <- fkl2VL e2
            p                  <- lift $ vlBinExpr o p1 p2
            return $ VShape p lyt
        UnOp _ (NotLifted o) e1 -> do
            SShape p1 lyt <- fkl2VL e1
            p              <- lift $ vlUnExpr o p1
            return $ SShape p lyt
        UnOp _ (Lifted o) e1 -> do
            VShape p1 lyt <- fkl2VL e1
            p                  <- lift $ vlUnExpr o p1
            return $ VShape p lyt
        If _ eb e1 e2 -> do
            eb' <- fkl2VL eb
            e1' <- fkl2VL e1
            e2' <- fkl2VL e2
            lift $ V.ifList eb' e1' e2'
        PApp1 t f arg -> do
            arg' <- fkl2VL arg
            lift $ papp1 t f arg'
        PApp2 _ f arg1 arg2 -> do
            arg1' <- fkl2VL arg1
            arg2' <- fkl2VL arg2
            lift $ papp2 f arg1' arg2'
        PApp3 _ p arg1 arg2 arg3 -> do
            arg1' <- fkl2VL arg1
            arg2' <- fkl2VL arg2
            arg3' <- fkl2VL arg3
            lift $ papp3 p arg1' arg2' arg3'
        QConcat n _ arg -> do
            arg' <- fkl2VL arg
            return $ V.qConcat n arg'
        UnConcat n _ arg1 arg2 -> do
            arg1' <- fkl2VL arg1
            arg2' <- fkl2VL arg2
            return $ V.unconcat n arg1' arg2'


papp3 :: Lifted Prim3 -> Shape VLDVec -> Shape VLDVec -> Shape VLDVec -> Build VL.VL (Shape VLDVec)
papp3 (Lifted Combine)    = V.combineL
papp3 (NotLifted Combine) = V.combine

papp1 :: Type -> Lifted Prim1 -> Shape VLDVec -> Build VL.VL (Shape VLDVec)
papp1 t (Lifted f) =
    case f of
        Length          -> V.lengthL
        Concat          -> V.concatL
        The             -> V.theL
        Fst             -> V.fstL
        Snd             -> V.sndL
        Tail            -> V.tailL
        Reverse         -> V.reverseL
        Init            -> V.initL
        Last            -> V.lastL
        Nub             -> V.nubL
        Number          -> V.numberL
        Transpose       -> V.transposeL
        Reshape n       -> V.reshapeL n
        And             -> V.aggrL VL.AggrAll
        Or              -> V.aggrL VL.AggrAny
        Minimum         -> V.aggrL VL.AggrMin
        Maximum         -> V.aggrL VL.AggrMax
        Sum             -> V.aggrL $ VL.AggrSum $ typeToRowType $ elemT t
        Avg             -> V.aggrL VL.AggrAvg

papp1 t (NotLifted f) =
    case f of
        Length           -> V.length
        Reshape n        -> V.reshape n
        Transpose        -> V.transpose
        Number           -> V.number
        Nub              -> V.nub
        Last             -> V.last
        Init             -> V.init
        Reverse          -> V.reverse
        Tail             -> V.tail
        Concat           -> V.concat
        Fst              -> V.fst
        Snd              -> V.snd
        The              -> V.the
        Sum              -> V.aggr $ VL.AggrSum $ typeToRowType t
        Avg              -> V.aggr VL.AggrAvg
        Or               -> V.aggr VL.AggrAny
        And              -> V.aggr VL.AggrAll
        Maximum          -> V.aggr VL.AggrMax
        Minimum          -> V.aggr VL.AggrMin

papp2 :: Lifted Prim2 -> Shape VLDVec -> Shape VLDVec -> Build VL.VL (Shape VLDVec)
papp2 (Lifted f) =
    case f of
        Dist           -> V.distL
        Group          -> V.groupL
        Sort           -> V.sortL
        Restrict       -> V.restrictL
        Pair           -> V.pairL
        Append         -> V.appendL
        Index          -> V.indexL
        Zip            -> V.zipL
        Cons           -> V.consL
        CartProduct    -> V.cartProductL
        NestProduct    -> V.nestProductL
        ThetaJoin p    -> V.thetaJoinL p
        NestJoin p     -> V.nestJoinL p
        SemiJoin p     -> V.semiJoinL p
        AntiJoin p     -> V.antiJoinL p

papp2 (NotLifted f) =
    case f of
        Dist            -> V.dist
        Group           -> V.group
        Sort            -> V.sort
        Restrict        -> V.restrict
        Pair            -> V.pair
        Append          -> V.append
        Index           -> V.index
        Zip             -> V.zip
        Cons            -> V.cons
        CartProduct     -> V.cartProduct
        NestProduct     -> V.nestProduct
        ThetaJoin p     -> V.thetaJoin p
        NestJoin p      -> V.nestJoin p
        SemiJoin p      -> V.semiJoin p
        AntiJoin p      -> V.antiJoin p

-- For each top node, determine the number of columns the vector has and insert
-- a dummy projection which just copies those columns. This is to ensure that
-- columns which are required from the top are not pruned by optimizations.
insertTopProjections :: Build VL.VL (Shape VLDVec) -> Build VL.VL (Shape VLDVec)
insertTopProjections g = g >>= traverseShape

  where
    traverseShape :: Shape VLDVec -> Build VL.VL (Shape VLDVec)
    traverseShape (VShape (VLDVec q) lyt) =
        insertProj lyt q VL.Project VLDVec VShape
    traverseShape (SShape (VLDVec q) lyt)     =
        insertProj lyt q VL.Project VLDVec SShape

    traverseLayout :: (Layout VLDVec) -> Build VL.VL (Layout VLDVec)
    traverseLayout (LCol c) =
        return $ LCol c
    traverseLayout (LPair lyt1 lyt2) = do
        lyt1' <- traverseLayout lyt1
        lyt2' <- traverseLayout lyt2
        return $ LPair lyt1' lyt2'
    traverseLayout (LNest (VLDVec q) lyt) =
      insertProj lyt q VL.Project VLDVec LNest

    insertProj
      :: Layout VLDVec               -- ^ The node's layout
      -> Alg.AlgNode                    -- ^ The top node to consider
      -> ([VL.Expr] -> VL.UnOp)         -- ^ Constructor for the projection op
      -> (Alg.AlgNode -> v)             -- ^ Vector constructor
      -> (v -> (Layout VLDVec) -> t) -- ^ Layout/Shape constructor
      -> Build VL.VL t
    insertProj lyt q project vector describe = do
        let width = columnsInLayout lyt
            cols  = [1 .. width]
        qp   <- insert $ Alg.UnOp (project $ map VL.Column cols) q
        lyt' <- traverseLayout lyt
        return $ describe (vector qp) lyt'

-- | Compile a FKL expression into a query plan of vector operators (VL)
specializeVectorOps :: FExpr -> QueryPlan VL.VL VLDVec
specializeVectorOps e = mkQueryPlan opMap shape tagMap
  where
    (opMap, shape, tagMap) = runBuild (insertTopProjections $ runReaderT (fkl2VL e) [])
