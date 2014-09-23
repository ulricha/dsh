{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections   #-}

module Database.DSH.Translate.FKL2VL (specializeVectorOps) where

import           Control.Applicative              hiding (Const)
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
import           Database.DSH.VL.Render.JSON      ()
import           Database.DSH.VL.Vector
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
        BinOp _ o NotLifted e1 e2    -> do
            SShape p1 lyt <- fkl2VL e1
            SShape p2 _   <- fkl2VL e2
            p              <- lift $ vlBinExpr o p1 p2
            return $ SShape p lyt
        BinOp _ o Lifted e1 e2     -> do
            VShape p1 lyt <- fkl2VL e1
            VShape p2 _   <- fkl2VL e2
            p                  <- lift $ vlBinExpr o p1 p2
            return $ VShape p lyt
        UnOp _ o NotLifted e1 -> do
            SShape p1 lyt <- fkl2VL e1
            p              <- lift $ vlUnExpr o p1
            return $ SShape p lyt
        UnOp _ o Lifted e1 -> do
            VShape p1 lyt <- fkl2VL e1
            p                  <- lift $ vlUnExpr o p1
            return $ VShape p lyt
        If _ eb e1 e2 -> do
            eb' <- fkl2VL eb
            e1' <- fkl2VL e1
            e2' <- fkl2VL e2
            lift $ V.ifList eb' e1' e2'
        PApp1 t f l arg -> do
            arg' <- fkl2VL arg
            lift $ papp1 t f l arg'
        PApp2 _ f l arg1 arg2 -> do
            arg1' <- fkl2VL arg1
            arg2' <- fkl2VL arg2
            lift $ papp2 f l arg1' arg2'
        PApp3 _ p l arg1 arg2 arg3 -> do
            arg1' <- fkl2VL arg1
            arg2' <- fkl2VL arg2
            arg3' <- fkl2VL arg3
            lift $ papp3 p l arg1' arg2' arg3'
        QConcat n _ arg -> do
            arg' <- fkl2VL arg
            return $ V.qConcat n arg'
        UnConcat n _ arg1 arg2 -> do
            arg1' <- fkl2VL arg1
            arg2' <- fkl2VL arg2
            return $ V.unconcat n arg1' arg2'
        MkTuple _ Lifted args -> do
            args' <- mapM fkl2VL args
            lift $ V.tuple args'
        MkTuple _ NotLifted args -> do
            args' <- mapM fkl2VL args
            lift $ V.tupleL args'

papp3 :: Prim3 -> Lifted -> Shape VLDVec -> Shape VLDVec -> Shape VLDVec -> Build VL.VL (Shape VLDVec)
papp3 Combine Lifted    = V.combineL
papp3 Combine NotLifted = V.combine

papp1 :: Type -> Prim1 -> Lifted -> Shape VLDVec -> Build VL.VL (Shape VLDVec)
papp1 t f Lifted =
    case f of
        Length          -> V.lengthL
        Concat          -> V.concatL
        The             -> V.theL
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
        Sum             -> V.aggrL $ VL.AggrSum $ typeToScalarType $ elemT t
        Avg             -> V.aggrL VL.AggrAvg
        TupElem i       -> V.tupElemL i

papp1 t f NotLifted =
    case f of
        Length           -> V.length_
        Reshape n        -> V.reshape n
        Transpose        -> V.transpose
        Number           -> V.number
        Nub              -> V.nub
        Last             -> V.last
        Init             -> V.init
        Reverse          -> V.reverse
        Tail             -> V.tail
        Concat           -> V.concat
        The              -> V.the
        Sum              -> V.aggr $ VL.AggrSum $ typeToScalarType t
        Avg              -> V.aggr VL.AggrAvg
        Or               -> V.aggr VL.AggrAny
        And              -> V.aggr VL.AggrAll
        Maximum          -> V.aggr VL.AggrMax
        Minimum          -> V.aggr VL.AggrMin
        TupElem i        -> V.tupElem i

papp2 :: Prim2 -> Lifted -> Shape VLDVec -> Shape VLDVec -> Build VL.VL (Shape VLDVec)
papp2 f Lifted =
    case f of
        Dist           -> V.distL
        Group          -> V.groupL
        Sort           -> V.sortL
        Restrict       -> V.restrictL
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

papp2 f NotLifted =
    case f of
        Dist            -> V.dist
        Group           -> V.group
        Sort            -> V.sort
        Restrict        -> V.restrict
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
    traverseLayout (LCol c)               = return $ LCol c
    traverseLayout (LTuple lyts)          = LTuple <$> mapM traverseLayout lyts
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
