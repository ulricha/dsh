{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TupleSections   #-}

module Database.DSH.SL.Vectorize
    ( vectorize
    ) where

import           Control.Monad.Reader

import           Database.Algebra.Dag.Build

import           Database.DSH.Common.Impossible
import           Database.DSH.Common.Lang
import           Database.DSH.Common.Pretty     hiding (forget)
import           Database.DSH.Common.QueryPlan
import           Database.DSH.Common.Type
import           Database.DSH.Common.Vector
import qualified Database.DSH.Common.VectorLang as VL
import           Database.DSH.FKL.Lang
import qualified Database.DSH.SL.Builtins       as Builtins
import           Database.DSH.SL.Construct
import qualified Database.DSH.SL.Lang           as SL

--------------------------------------------------------------------------------
-- Extend the DAG builder monad with an environment for compiled SL
-- DAGs.

type Env = [(String, Shape DVec)]

type EnvBuild = ReaderT Env (Build SL.TSL)

lookupEnv :: String -> EnvBuild (Shape DVec)
lookupEnv n = ask >>= \env -> case lookup n env of
    Just r  -> return r
    Nothing -> error $ "SL.Vectorize.lookupEnv: " ++ n

bind :: Ident -> Shape DVec -> Env -> Env
bind n e env = (n, e) : env

--------------------------------------------------------------------------------
-- Compilation from FKL expressions to a SL DAG.

fkl2SL :: FExpr -> EnvBuild (Shape DVec)
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
            VShape p1 lyt <- fkl2SL e1
            p                  <- lift $ slUnExpr o p1
            return $ VShape p lyt
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
        UnOp _ _ NotLifted _ -> $impossible
        BinOp _ _ NotLifted _ _    -> $impossible
        If{} -> $impossible
        MkTuple _ NotLifted _ -> $impossible

papp3 :: Prim3 -> Lifted -> Shape DVec -> Shape DVec -> Shape DVec -> Build SL.TSL (Shape DVec)
papp3 Combine Lifted    = Builtins.combineL
papp3 Combine NotLifted = Builtins.combine

aggL :: Type -> AggrFun -> Shape DVec -> Build SL.TSL (Shape DVec)
aggL t Sum     = Builtins.aggrL (VL.AggrSum $ VL.typeToScalarType $ elemT t)
aggL _ Avg     = Builtins.aggrL VL.AggrAvg
aggL _ Maximum = Builtins.aggrL VL.AggrMax
aggL _ Minimum = Builtins.aggrL VL.AggrMin
aggL _ Or      = Builtins.aggrL VL.AggrAny
aggL _ And     = Builtins.aggrL VL.AggrAll
aggL _ Length  = Builtins.lengthL

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

papp1 :: Type -> Prim1 -> Lifted -> Shape DVec -> Build SL.TSL (Shape DVec)
papp1 t f Lifted =
    case f of
        Singleton       -> Builtins.singletonL
        Only            -> Builtins.onlyL
        Concat          -> Builtins.concatL
        Reverse         -> Builtins.reverseL
        Nub             -> Builtins.nubL
        Number          -> Builtins.numberL
        Sort            -> Builtins.sortL
        Group           -> Builtins.groupL
        Restrict        -> Builtins.restrictL
        Agg a           -> aggL t a
        TupElem i       -> Builtins.tupElemL i
        LitExt v        -> Builtins.extL v

papp1 _ f NotLifted =
    case f of
        Concat           -> Builtins.concat
        Restrict         -> Builtins.restrict
        o                -> error $ (pp o) ++ " not lifted"

papp2 :: Prim2 -> Lifted -> Shape DVec -> Shape DVec -> Build SL.TSL (Shape DVec)
papp2 f Lifted =
    case f of
        Dist                -> Builtins.distL
        Append              -> Builtins.appendL
        Zip                 -> Builtins.zipL
        CartProduct         -> Builtins.cartProductL
        ThetaJoin p         -> Builtins.thetaJoinL p
        NestJoin p          -> Builtins.nestJoinL p
        GroupJoin p (NE as) -> Builtins.groupJoinL p (NE $ fmap translateAggrFun as)
        SemiJoin p          -> Builtins.semiJoinL p
        AntiJoin p          -> Builtins.antiJoinL p

papp2 f NotLifted =
    case f of
        Dist                -> Builtins.dist
        _                   -> $impossible

-- | Compile a FKL expression into a query plan of vector operators (SL)
vectorize :: FExpr -> QueryPlan SL.TSL DVec
vectorize e = mkQueryPlan opMap shape tagMap
  where
    (opMap, shape, tagMap) = runBuild (runReaderT (fkl2SL e) [])
