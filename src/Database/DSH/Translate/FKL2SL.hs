{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections   #-}

module Database.DSH.Translate.FKL2SL (specializeVectorOps) where

import           Control.Monad.Reader

import           Database.Algebra.Dag.Build
import qualified Database.Algebra.Dag.Common    as Alg

import           Database.DSH.Common.Impossible
import           Database.DSH.Common.Lang
import           Database.DSH.Common.QueryPlan
import           Database.DSH.Common.Type
import           Database.DSH.Common.Vector
import qualified Database.DSH.Common.VectorLang as SL
import           Database.DSH.FKL.Lang
import qualified Database.DSH.SL.Lang           as SL
import           Database.DSH.SL.Primitives
import qualified Database.DSH.SL.Vectorize      as V

--------------------------------------------------------------------------------
-- Extend the DAG builder monad with an environment for compiled SL
-- DAGs.

type Env = [(String, Shape SLDVec)]

type EnvBuild = ReaderT Env (Build SL.SL)

-- FIXME might need those when let-expressions have been introduced.
lookupEnv :: String -> EnvBuild (Shape SLDVec)
lookupEnv n = ask >>= \env -> case lookup n env of
    Just r -> return r
    Nothing -> $impossible

bind :: Ident -> Shape SLDVec -> Env -> Env
bind n e env = (n, e) : env

--------------------------------------------------------------------------------
-- Compilation from FKL expressions to a SL DAG.

fkl2SL :: FExpr -> EnvBuild (Shape SLDVec)
fkl2SL expr =
    case expr of
        Var _ n -> lookupEnv n
        Let _ n e1 e -> do
            e1' <- fkl2SL e1
            local (bind n e1') $ fkl2SL e
        Table _ n schema -> lift $ V.dbTable n schema
        Const t v -> lift $ V.shredLiteral t v
        BinOp _ o NotLifted e1 e2    -> do
            s1 <- fkl2SL e1
            s2 <- fkl2SL e2
            lift $ V.binOp o s1 s2
        BinOp _ o Lifted e1 e2     -> do
            s1 <- fkl2SL e1
            s2 <- fkl2SL e2
            lift $ V.binOpL o s1 s2
        UnOp _ o NotLifted e1 -> do
            SShape p1 lyt <- fkl2SL e1
            p              <- lift $ slUnExpr o p1
            return $ SShape p lyt
        UnOp _ o Lifted e1 -> do
            VShape p1 lyt <- fkl2SL e1
            p                  <- lift $ slUnExpr o p1
            return $ VShape p lyt
        If _ eb e1 e2 -> do
            eb' <- fkl2SL eb
            e1' <- fkl2SL e1
            e2' <- fkl2SL e2
            lift $ V.ifList eb' e1' e2'
        PApp1 t f l arg -> do
            arg' <- fkl2SL arg
            lift $ papp1 t f l arg'
        PApp2 _ f l arg1 arg2 -> do
            arg1' <- fkl2SL arg1
            arg2' <- fkl2SL arg2
            lift $ papp2 f l arg1' arg2'
        PApp3 _ p l arg1 arg2 arg3 -> do
            arg1' <- fkl2SL arg1
            arg2' <- fkl2SL arg2
            arg3' <- fkl2SL arg3
            lift $ papp3 p l arg1' arg2' arg3'
        Ext (Forget n _ arg) -> do
            arg' <- fkl2SL arg
            return $ V.forget n arg'
        Ext (Imprint n _ arg1 arg2) -> do
            arg1' <- fkl2SL arg1
            arg2' <- fkl2SL arg2
            return $ V.imprint n arg1' arg2'
        MkTuple _ Lifted args -> do
            args' <- mapM fkl2SL args
            lift $ V.tupleL args'
        MkTuple _ NotLifted args -> do
            args' <- mapM fkl2SL args
            lift $ V.tuple args'

papp3 :: Prim3 -> Lifted -> Shape SLDVec -> Shape SLDVec -> Shape SLDVec -> Build SL.SL (Shape SLDVec)
papp3 Combine Lifted    = V.combineL
papp3 Combine NotLifted = V.combine

aggL :: Type -> AggrFun -> Shape SLDVec -> Build SL.SL (Shape SLDVec)
aggL t Sum     = V.aggrL (SL.AggrSum $ typeToScalarType $ elemT t)
aggL _ Avg     = V.aggrL SL.AggrAvg
aggL _ Maximum = V.aggrL SL.AggrMax
aggL _ Minimum = V.aggrL SL.AggrMin
aggL _ Or      = V.aggrL SL.AggrAny
aggL _ And     = V.aggrL SL.AggrAll
aggL _ Length  = V.lengthL

agg :: Type -> AggrFun -> Shape SLDVec -> Build SL.SL (Shape SLDVec)
agg t Sum     = V.aggr (SL.AggrSum $ typeToScalarType t)
agg _ Avg     = V.aggr SL.AggrAvg
agg _ Maximum = V.aggr SL.AggrMax
agg _ Minimum = V.aggr SL.AggrMin
agg _ Or      = V.aggr SL.AggrAny
agg _ And     = V.aggr SL.AggrAll
agg _ Length  = V.length_

translateAggrFun :: AggrApp -> SL.AggrFun
translateAggrFun a = case aaFun a of
    Sum     -> let t = typeToScalarType $ typeOf $ aaArg a
               in SL.AggrSum t e
    Avg     -> SL.AggrAvg e
    Maximum -> SL.AggrMax e
    Minimum -> SL.AggrMin e
    Or      -> SL.AggrAny e
    And     -> SL.AggrAll e
    Length  -> SL.AggrCount
  where
    e = scalarExpr $ aaArg a

papp1 :: Type -> Prim1 -> Lifted -> Shape SLDVec -> Build SL.SL (Shape SLDVec)
papp1 t f Lifted =
    case f of
        Singleton       -> V.singletonL
        Only            -> V.onlyL
        Concat          -> V.concatL
        Reverse         -> V.reverseL
        Nub             -> V.nubL
        Number          -> V.numberL
        Sort            -> V.sortL
        Group           -> V.groupL
        Restrict        -> V.restrictL
        Agg a           -> aggL t a
        TupElem i       -> V.tupElemL i

papp1 t f NotLifted =
    case f of
        Singleton        -> V.singleton
        Only             -> V.only
        Number           -> V.number
        Sort             -> V.sort
        Group            -> V.group
        Restrict         -> V.restrict
        Nub              -> V.nub
        Reverse          -> V.reverse
        Concat           -> V.concat
        Agg a            -> agg t a
        TupElem i        -> V.tupElem i

papp2 :: Prim2 -> Lifted -> Shape SLDVec -> Shape SLDVec -> Build SL.SL (Shape SLDVec)
papp2 f Lifted =
    case f of
        Dist                -> V.distL
        Append              -> V.appendL
        Zip                 -> V.zipL
        CartProduct         -> V.cartProductL
        ThetaJoin p         -> V.thetaJoinL p
        NestJoin p          -> V.nestJoinL p
        GroupJoin p (NE as) -> V.groupJoinL p (NE $ fmap translateAggrFun as)
        SemiJoin p          -> V.semiJoinL p
        AntiJoin p          -> V.antiJoinL p

papp2 f NotLifted =
    case f of
        Dist                -> V.dist
        Append              -> V.append
        Zip                 -> V.zip
        CartProduct         -> V.cartProduct
        ThetaJoin p         -> V.thetaJoin p
        NestJoin p          -> V.nestJoin p
        GroupJoin p (NE as) -> V.groupJoin p (NE $ fmap translateAggrFun as)
        SemiJoin p          -> V.semiJoin p
        AntiJoin p          -> V.antiJoin p

-- For each top node, determine the number of columns the vector has and insert
-- a dummy projection which just copies those columns. This is to ensure that
-- columns which are required from the top are not pruned by optimizations.
insertTopProjections :: Build SL.SL (Shape SLDVec) -> Build SL.SL (Shape SLDVec)
insertTopProjections g = g >>= traverseShape

  where
    traverseShape :: Shape SLDVec -> Build SL.SL (Shape SLDVec)
    traverseShape (VShape (SLDVec q) lyt) =
        insertProj lyt q VShape
    traverseShape (SShape (SLDVec q) lyt)     =
        insertProj lyt q SShape

    traverseLayout :: Layout SLDVec -> Build SL.SL (Layout SLDVec)
    traverseLayout LCol                   = return LCol
    traverseLayout (LTuple lyts)          = LTuple <$> mapM traverseLayout lyts
    traverseLayout (LNest (SLDVec q) lyt) =
      insertProj lyt q LNest

    insertProj :: Layout SLDVec                  -- ^ The node's layout
               -> Alg.AlgNode                    -- ^ The top node to consider
               -> (SLDVec -> Layout SLDVec -> t) -- ^ Layout/Shape constructor
               -> Build SL.SL t
    insertProj lyt q describe = do
        let width = columnsInLayout lyt
            cols  = [1 .. width]
        qp   <- insert $ Alg.UnOp (SL.Project $ map SL.Column cols) q
        lyt' <- traverseLayout lyt
        return $ describe (SLDVec qp) lyt'

-- | Compile a FKL expression into a query plan of vector operators (SL)
specializeVectorOps :: FExpr -> QueryPlan SL.SL SLDVec
specializeVectorOps e = mkQueryPlan opMap shape tagMap
  where
    (opMap, shape, tagMap) = runBuild (insertTopProjections $ runReaderT (fkl2SL e) [])
