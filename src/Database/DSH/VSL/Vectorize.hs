{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.VSL.Vectorize
    ( vectorizeDelayed
    )where

import           Control.Monad.Reader

import           Database.Algebra.Dag.Build

import           Database.DSH.Common.Impossible
import           Database.DSH.Common.Lang
import           Database.DSH.Common.QueryPlan
import           Database.DSH.Common.Type
import           Database.DSH.Common.Vector
import qualified Database.DSH.Common.VectorLang as VL
import           Database.DSH.FKL.Lang
import qualified Database.DSH.VSL.Builtins      as Builtins
import           Database.DSH.VSL.Construct     (VSLBuild)
import           Database.DSH.VSL.Lang          (TVSL)

--------------------------------------------------------------------------------
-- Extend the DAG builder monad with an environment for compiled SL
-- DAGs.

type Env = [(String, Shape Builtins.DelayedVec)]

type EnvBuild = ReaderT Env (VSLBuild VL.TExpr VL.TExpr)

lookupEnv :: String -> EnvBuild (Shape Builtins.DelayedVec)
lookupEnv n = ask >>= \env -> case lookup n env of
    Just r -> return r
    Nothing -> $impossible

bind :: Ident -> Shape Builtins.DelayedVec -> Env -> Env
bind n e env = (n, e) : env

--------------------------------------------------------------------------------
-- Compilation from FKL expressions to a VSL DAG.

fkl2SL :: FExpr -> EnvBuild (Shape Builtins.DelayedVec)
fkl2SL expr =
    case expr of
        Var _ n -> lookupEnv n
        Let _ n e1 e -> do
            e1' <- fkl2SL e1
            local (bind n e1') $ fkl2SL e
        Table _ n schema -> lift $ Builtins.dbTable n schema
        Const t vs -> lift $ Builtins.shredLiteral t (ListV vs)
        BinOp _ o Lifted e1 e2     -> do
            s1 <- fkl2SL e1
            s2 <- fkl2SL e2
            lift $ Builtins.binOpL o s1 s2
        UnOp _ o Lifted e1 -> do
            s1 <- fkl2SL e1
            lift $ Builtins.unOpL o s1
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
            lift $ Builtins.tupleL args'
        MkTuple _ NotLifted _ -> $impossible
        UnOp _ _ NotLifted _ -> $impossible
        BinOp _ _ NotLifted _ _ -> $impossible

papp3 :: Prim3 -> Lifted -> Shape Builtins.DelayedVec -> Shape Builtins.DelayedVec -> Shape Builtins.DelayedVec -> Build TVSL (Shape Builtins.DelayedVec)
papp3 Combine Lifted    = Builtins.terMacroL Builtins.combine
papp3 Combine NotLifted = $impossible

aggL :: Type -> AggrFun -> Shape Builtins.DelayedVec -> Build TVSL (Shape Builtins.DelayedVec)
aggL t Sum     = Builtins.aggrL (VL.AggrSum $ VL.typeToScalarType $ elemT t)
aggL _ Avg     = Builtins.aggrL VL.AggrAvg
aggL _ Maximum = Builtins.aggrL VL.AggrMax
aggL _ Minimum = Builtins.aggrL VL.AggrMin
aggL _ Or      = Builtins.aggrL VL.AggrAny
aggL _ And     = Builtins.aggrL VL.AggrAll
aggL _ Length  = Builtins.aggrL (const VL.AggrCount)

translateAggrFun :: AggrApp -> VL.AggrFun VL.TExpr
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

papp1 :: Type -> Prim1 -> Lifted -> Shape Builtins.DelayedVec -> Build TVSL (Shape Builtins.DelayedVec)
papp1 t f Lifted =
    case f of
        Singleton       -> Builtins.sngL
        Only            -> Builtins.onlyL
        Concat          -> Builtins.concatL
        Reverse         -> Builtins.unMacroL Builtins.reverse
        Nub             -> Builtins.unMacroL Builtins.nub
        Number          -> Builtins.unMacroL Builtins.number
        Sort            -> Builtins.unMacroL Builtins.sort
        Group           -> Builtins.unMacroL Builtins.group
        Restrict        -> Builtins.unMacroL Builtins.restrict
        LitExt v        -> Builtins.unMacroL (Builtins.ext v)
        Agg a           -> aggL t a
        TupElem i       -> Builtins.tupElemL i

papp1 _ _ NotLifted = $impossible

papp2 :: Prim2 -> Lifted -> Shape Builtins.DelayedVec -> Shape Builtins.DelayedVec -> Build TVSL (Shape Builtins.DelayedVec)
papp2 f Lifted =
    case f of
        Dist                -> Builtins.distL
        Append              -> Builtins.binMacroL Builtins.append
        Zip                 -> Builtins.binMacroL Builtins.zip
        CartProduct         -> Builtins.binMacroL Builtins.cartproduct
        ThetaJoin p         -> Builtins.binMacroL $ Builtins.thetajoin p
        NestJoin p          -> Builtins.binMacroL $ Builtins.nestjoin p
        GroupJoin p (NE as) -> Builtins.binMacroL $ Builtins.groupjoin p (NE $ fmap translateAggrFun as)
        SemiJoin p          -> Builtins.binMacroL $ Builtins.semijoin p
        AntiJoin p          -> Builtins.binMacroL $ Builtins.antijoin p

papp2 _ NotLifted = $impossible

--------------------------------------------------------------------------------

-- | Materialize a result vector
finalizeResultVectors :: Shape Builtins.DelayedVec -> Build TVSL (Shape DVec)
finalizeResultVectors (VShape dv l) = finalizeShape dv l VShape

finalizeShape :: Builtins.DelayedVec -> Layout Builtins.DelayedVec -> (DVec -> Layout DVec -> t) -> Build TVSL t
finalizeShape dv l shapeConst = do
    (v', l') <- Builtins.materializeShape dv l
    l''      <- traverseLayout l'
    return $ shapeConst v' l''

traverseLayout :: Layout Builtins.DelayedVec -> Build TVSL (Layout DVec)
traverseLayout LCol        = return LCol
traverseLayout (LTuple ls) = LTuple <$> mapM traverseLayout ls
traverseLayout (LNest v l) = finalizeShape v l LNest

--------------------------------------------------------------------------------

-- | Compile a FKL expression into a query plan of vector operators (SL)
vectorizeDelayed :: FExpr -> QueryPlan TVSL DVec
vectorizeDelayed e = mkQueryPlan opMap shape tagMap
  where
    (opMap, shape, tagMap) = runBuild $ runReaderT (fkl2SL e) [] >>= finalizeResultVectors
