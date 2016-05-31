{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.Translate.FKL2VSL where

import           Control.Monad.Reader

import           Database.Algebra.Dag.Build

import           Database.DSH.Common.Impossible
import           Database.DSH.Common.Lang
import           Database.DSH.Common.QueryPlan
import           Database.DSH.Common.Type
import           Database.DSH.Common.Vector
import qualified Database.DSH.Common.VectorLang as VL
import           Database.DSH.FKL.Lang
import           Database.DSH.VSL.Construct     (VSLBuild)
import qualified Database.DSH.VSL.Construct     as C
import           Database.DSH.VSL.Lang          (VSL)
import qualified Database.DSH.VSL.Vectorize     as V

--------------------------------------------------------------------------------
-- Extend the DAG builder monad with an environment for compiled SL
-- DAGs.

type Env = [(String, Shape V.DelayedVec)]

type EnvBuild = ReaderT Env VSLBuild

lookupEnv :: String -> EnvBuild (Shape V.DelayedVec)
lookupEnv n = ask >>= \env -> case lookup n env of
    Just r -> return r
    Nothing -> $impossible

bind :: Ident -> Shape V.DelayedVec -> Env -> Env
bind n e env = (n, e) : env

--------------------------------------------------------------------------------
-- Compilation from FKL expressions to a VSL DAG.

fkl2SL :: FExpr -> EnvBuild (Shape V.DelayedVec)
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
            s1 <- fkl2SL e1
            lift $ V.unOp o s1
        UnOp _ o Lifted e1 -> do
            s1 <- fkl2SL e1
            lift $ V.unOpL o s1
        If _ eb e1 e2 -> do
            eb' <- fkl2SL eb
            e1' <- fkl2SL e1
            e2' <- fkl2SL e2
            lift $ V.if_ eb' e1' e2'
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
            return $ forget n arg'
        Ext (Imprint n _ arg1 arg2) -> do
            arg1' <- fkl2SL arg1
            arg2' <- fkl2SL arg2
            return $ imprint n arg1' arg2'
        MkTuple _ Lifted args -> do
            args' <- mapM fkl2SL args
            lift $ V.tupleL args'
        MkTuple _ NotLifted args -> do
            args' <- mapM fkl2SL args
            lift $ V.tuple args'

papp3 :: Prim3 -> Lifted -> Shape V.DelayedVec -> Shape V.DelayedVec -> Shape V.DelayedVec -> VSLBuild (Shape V.DelayedVec)
papp3 Combine Lifted    = V.terMacroL V.combine
papp3 Combine NotLifted = V.terMacro V.combine

aggL :: Type -> AggrFun -> Shape V.DelayedVec -> VSLBuild (Shape V.DelayedVec)
aggL t Sum     = V.aggrL (VL.AggrSum $ VL.typeToScalarType $ elemT t)
aggL _ Avg     = V.aggrL VL.AggrAvg
aggL _ Maximum = V.aggrL VL.AggrMax
aggL _ Minimum = V.aggrL VL.AggrMin
aggL _ Or      = V.aggrL VL.AggrAny
aggL _ And     = V.aggrL VL.AggrAll
aggL _ Length  = V.aggrL (const VL.AggrCount)

agg :: Type -> AggrFun -> Shape V.DelayedVec -> VSLBuild (Shape V.DelayedVec)
agg t Sum     = V.aggr (VL.AggrSum $ VL.typeToScalarType t)
agg _ Avg     = V.aggr VL.AggrAvg
agg _ Maximum = V.aggr VL.AggrMax
agg _ Minimum = V.aggr VL.AggrMin
agg _ Or      = V.aggr VL.AggrAny
agg _ And     = V.aggr VL.AggrAll
agg _ Length  = V.aggr (const VL.AggrCount)

translateAggrFun :: AggrApp -> VL.AggrFun
translateAggrFun a = case aaFun a of
    Sum     -> let t = VL.typeToScalarType $ typeOf $ aaArg a
               in VL.AggrSum t e
    Avg     -> VL.AggrAvg e
    Maximum -> VL.AggrMax e
    Minimum -> VL.AggrMin e
    Or      -> VL.AggrAny e
    And     -> VL.AggrAll e
    Length  -> VL.AggrCount
  where
    e = VL.scalarExpr $ aaArg a

papp1 :: Type -> Prim1 -> Lifted -> Shape V.DelayedVec -> VSLBuild (Shape V.DelayedVec)
papp1 t f Lifted =
    case f of
        Singleton       -> V.sngL
        Only            -> V.onlyL
        Concat          -> V.concatL
        Reverse         -> V.unMacroL V.reverse
        Nub             -> V.unMacroL V.nub
        Number          -> V.unMacroL V.number
        Sort            -> V.unMacroL V.sort
        Group           -> V.unMacroL V.group
        Restrict        -> V.unMacroL V.restrict
        Agg a           -> aggL t a
        TupElem i       -> V.tupElemL i

papp1 t f NotLifted =
    case f of
        Singleton        -> V.sng
        Only             -> V.only
        Number           -> V.unMacro V.number
        Sort             -> V.unMacro V.sort
        Group            -> V.unMacro V.group
        Restrict         -> V.unMacro V.restrict
        Nub              -> V.unMacro V.nub
        Reverse          -> V.unMacro V.reverse
        Concat           -> V.concat
        Agg a            -> agg t a
        TupElem i        -> V.tupElem i

papp2 :: Prim2 -> Lifted -> Shape V.DelayedVec -> Shape V.DelayedVec -> VSLBuild (Shape V.DelayedVec)
papp2 f Lifted =
    case f of
        Dist                -> V.distL
        Append              -> V.binMacroL V.append
        Zip                 -> V.binMacroL V.zip
        CartProduct         -> V.binMacroL V.cartproduct
        ThetaJoin p         -> V.binMacroL $ V.thetajoin p
        NestJoin p          -> V.binMacroL $ V.nestjoin p
        GroupJoin p (NE as) -> V.binMacroL $ V.groupjoin p (NE $ fmap translateAggrFun as)
        SemiJoin p          -> V.binMacroL $ V.semijoin p
        AntiJoin p          -> V.binMacroL $ V.antijoin p

papp2 f NotLifted =
    case f of
        Dist                -> V.dist
        Append              -> V.binMacro V.append
        Zip                 -> V.binMacro V.zip
        CartProduct         -> V.binMacro V.cartproduct
        ThetaJoin p         -> V.binMacro $ V.thetajoin p
        NestJoin p          -> V.binMacro $ V.nestjoin p
        GroupJoin p (NE as) -> V.binMacro $ V.groupjoin p (NE $ fmap translateAggrFun as)
        SemiJoin p          -> V.binMacro $ V.semijoin p
        AntiJoin p          -> V.binMacro $ V.antijoin p

--------------------------------------------------------------------------------

-- | Materialize a result vector and insert a projection for all its columns.
-- This ensures that no result columns will be pruned by rewrites.
finalizeResultVectors :: Shape V.DelayedVec -> VSLBuild (Shape DVec)
finalizeResultVectors (VShape dv l) = finalizeShape dv l VShape
finalizeResultVectors (SShape dv l) = finalizeShape dv l SShape

finalizeShape :: V.DelayedVec -> Layout V.DelayedVec -> (DVec -> Layout DVec -> t) -> VSLBuild t
finalizeShape dv l shapeConst = do
    (v', l') <- V.materializeShape dv l
    l''      <- traverseLayout l'

    let width = columnsInLayout l''
        cols  = map VL.Column [1 .. width]
    vp       <- C.project cols v'
    return $ shapeConst vp l''

traverseLayout :: Layout V.DelayedVec -> VSLBuild (Layout DVec)
traverseLayout LCol        = return LCol
traverseLayout (LTuple ls) = LTuple <$> mapM traverseLayout ls
traverseLayout (LNest v l) = finalizeShape v l LNest

--------------------------------------------------------------------------------

-- | Compile a FKL expression into a query plan of vector operators (SL)
specializeVectorOps :: FExpr -> QueryPlan VSL DVec
specializeVectorOps e = mkQueryPlan opMap shape tagMap
  where
    (opMap, shape, tagMap) = runBuild $ runReaderT (fkl2SL e) [] >>= finalizeResultVectors
