{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections   #-}

module Database.DSH.Translate.FKL2VL (specializeVectorOps) where

import           Control.Monad.Reader


import           Database.Algebra.Dag.Build
import qualified Database.Algebra.Dag.Common      as Alg

import           Database.DSH.Common.Type
import           Database.DSH.Common.Lang
import           Database.DSH.FKL.Lang
import           Database.DSH.Impossible
import           Database.DSH.VL.Vector
import qualified Database.DSH.VL.Lang             as VL
import           Database.DSH.VL.Render.JSON      ()
import           Database.DSH.Common.QueryPlan
import qualified Database.DSH.VL.VectorOperations as P
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

bind :: Ident -> Shape VLDVec -> Env -> Env
bind n e env = (n, e) : env

--------------------------------------------------------------------------------
-- Compilation from FKL expressions to a VL DAG.

fkl2VL :: Expr -> EnvBuild (Shape VLDVec)
fkl2VL expr =
    case expr of
        Var _ n -> lookupEnv n
        Let _ n e1 e -> do
            e1' <- fkl2VL e1
            local (bind n e1') $ fkl2VL e
        Table _ n cs hs -> lift $ P.dbTable n cs hs
        Const t v -> lift $ P.mkLiteral t v
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
            lift $ P.ifList eb' e1' e2'
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
            return $ P.qConcat n arg'
        UnConcat n _ arg1 arg2 -> do
            arg1' <- fkl2VL arg1
            arg2' <- fkl2VL arg2
            return $ P.unconcat n arg1' arg2'
             

papp3 :: Lifted Prim3 -> Shape VLDVec -> Shape VLDVec -> Shape VLDVec -> Build VL.VL (Shape VLDVec)
papp3 (Lifted Combine)    = P.combineL
papp3 (NotLifted Combine) = P.combine 

papp1 :: Type -> Lifted Prim1 -> Shape VLDVec -> Build VL.VL (Shape VLDVec)
papp1 t (Lifted f) =
    case f of
        Length          -> P.lengthL
        Concat          -> P.concatL
        The             -> P.theL
        Fst             -> P.fstL
        Snd             -> P.sndL
        Tail            -> P.tailL
        Reverse         -> P.reverseL
        Init            -> P.initL
        Last            -> P.lastL
        Nub             -> P.nubL
        Number          -> P.numberL
        Transpose       -> P.transposeL
        Reshape n       -> P.reshapeL n
        And             -> P.aggrL VL.AggrAll
        Or              -> P.aggrL VL.AggrAny
        Minimum         -> P.aggrL VL.AggrMin
        Maximum         -> P.aggrL VL.AggrMax
        Sum             -> P.aggrL $ VL.AggrSum $ typeToRowType $ elemT t
        Avg             -> P.aggrL VL.AggrAvg

papp1 t (NotLifted f) =
    case f of
        Length           -> P.length
        Reshape n        -> P.reshape n
        Transpose        -> P.transpose
        Number           -> P.number
        Nub              -> P.nub
        Last             -> P.last
        Init             -> P.init
        Reverse          -> P.reverse
        Tail             -> P.tail
        Concat           -> P.concat
        Fst              -> P.fst
        Snd              -> P.snd
        The              -> P.the
        Sum              -> P.aggr $ VL.AggrSum $ typeToRowType t
        Avg              -> P.aggr VL.AggrAvg
        Or               -> P.aggr VL.AggrAny
        And              -> P.aggr VL.AggrAll
        Maximum          -> P.aggr VL.AggrMax
        Minimum          -> P.aggr VL.AggrMin

papp2 :: Lifted Prim2 -> Shape VLDVec -> Shape VLDVec -> Build VL.VL (Shape VLDVec)
papp2 (Lifted f) =
    case f of
        Dist           -> P.distL
        Group          -> P.groupL
        Sort           -> P.sortL
        Restrict       -> P.restrictL
        Pair           -> P.pairL
        Append         -> P.appendL
        Index          -> P.indexL
        Zip            -> P.zipL
        Cons           -> P.consL
        CartProduct    -> P.cartProductL
        NestProduct    -> P.nestProductL
        ThetaJoin p    -> P.thetaJoinL p
        NestJoin p     -> P.nestJoinL p
        SemiJoin p     -> P.semiJoinL p
        AntiJoin p     -> P.antiJoinL p

papp2 (NotLifted f) =
    case f of
        Dist            -> P.dist
        Group           -> P.group
        Sort            -> P.sort
        Restrict        -> P.restrict
        Pair            -> P.pair
        Append          -> P.append
        Index           -> P.index
        Zip             -> P.zip
        Cons            -> P.cons
        CartProduct     -> P.cartProduct
        NestProduct     -> P.nestProduct
        ThetaJoin p     -> P.thetaJoin p
        NestJoin p      -> P.nestJoin p
        SemiJoin p      -> P.semiJoin p
        AntiJoin p      -> P.antiJoin p

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
        qp   <- insertNode $ Alg.UnOp (project $ map VL.Column cols) q
        lyt' <- traverseLayout lyt
        return $ describe (vector qp) lyt'

-- | Compile a FKL expression into a query plan of vector operators (VL)
specializeVectorOps :: Expr -> QueryPlan VL.VL VLDVec
specializeVectorOps e = mkQueryPlan opMap shape tagMap
  where
    (opMap, shape, tagMap) = runBuild (insertTopProjections $ runReaderT (fkl2VL e) [])
