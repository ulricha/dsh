-- | Infrastructure for fold/group fusion for group and nestjoin operators.
module Database.DSH.CL.Opt.FoldGroup
    ( GroupM
    , gaSubst
    , nextGaIdx
    , AggrMap
    , mkAggrMap
      -- * Transformations
    , traverseToHeadT
    , searchAggExpR
    , searchAggQualsR
    ) where

import           Control.Arrow
import           Data.List.NonEmpty            (NonEmpty ((:|)))
import qualified Data.Map                      as M

import           Database.DSH.Common.Kure
import           Database.DSH.Common.Lang
import           Database.DSH.Common.Nat

import           Database.DSH.CL.Kure
import           Database.DSH.CL.Lang

import qualified Database.DSH.CL.Primitives    as P

import           Database.DSH.CL.Opt.Auxiliary

--------------------------------------------------------------------------------
-- Infrastructure for Fold/Group Fusion

type GroupM = RewriteStateM (Maybe (Ident, AggrApp)) RewriteLog

gaSubst :: Expr -> [Type] -> Expr
gaSubst gaVar gaElemTy = P.tuple $ go First gaElemTy
  where
    go i (_ : tys) = P.tupElem i gaVar : go (Next i) tys
    go _ []        = []

nextGaIdx :: [Type] -> TupleIndex
nextGaIdx []        = First
nextGaIdx (_ : tys) = Next $ nextGaIdx tys

type AggrMap = M.Map AggrApp (TupleIndex, Ident)

mkAggrMap :: Ident -> NE AggrApp -> AggrMap
mkAggrMap n (NE (a :| as)) = go 4 as (M.insert a (3, n) M.empty)
  where
    go _ []         m = m
    go i (a' : as') m = go (Next i) as' (M.insert a' (i, n) m)


-- | Traverse qualifiers from the current candidate generator to the end. Once
-- reaching the end, traverse the head searching for an aggregate that matches
-- the candidate generator.
traverseToHeadT :: [Type] -> AggrMap -> Ident -> Expr -> Transform CompCtx GroupM CL Expr
traverseToHeadT groupElemTy aggMap x h = readerT $ \qs -> case qs of
    QualsCL (BindQ x' _ :* _)
        | x == x'   -> fail "shadowing"
        | otherwise -> childT QualsTail $ traverseToHeadT groupElemTy aggMap x h
    QualsCL (GuardQ _ :* _) -> childT QualsTail $ traverseToHeadT groupElemTy aggMap x h
    QualsCL (S (BindQ x' xs))
        | x == x'   -> fail "shadowing"
        | otherwise -> do
            ctx <- contextT
            let ctx' = ctx { clBindings = M.insert x' (elemT $ typeOf xs) (clBindings ctx) }
            constT (pure $ inject h) >>> withContextT ctx' (searchAggExpR groupElemTy aggMap x) >>> projectT
    QualsCL (S (GuardQ _)) -> do
        constT (pure $ inject h) >>> searchAggExpR groupElemTy aggMap x >>> projectT
    _ -> fail "no qualifiers"

-- | Search an expression for a matching aggregate. Replace aggregate on the
-- spot.
searchAggExpR :: [Type] -> AggrMap -> Ident -> Rewrite CompCtx GroupM CL
searchAggExpR groupElemTy aggMap x = readerT $ \cl -> case cl of
    ExprCL (AppE1 aggTy (Agg (Length False)) _) -> do
        agg <- AggrApp (Length True) <$> pathT [AppE1Arg, AppE1Arg] (toAggregateExprT x)
        case M.lookup agg aggMap of
            Just (gaIdx, gaName) -> do
                pure $ inject $ P.tupElem gaIdx (Var (TupleT groupElemTy) gaName)
            Nothing -> do
                gaName <- liftstateT $ freshNameT []
                let gaElemTy = TupleT $ groupElemTy ++ [aggTy]
                constT $ put $ Just (gaName, agg)
                pure $ inject $ P.tupElem (nextGaIdx groupElemTy) (Var gaElemTy gaName)
    ExprCL (AppE1 aggTy (Agg a) _) -> do
        agg <- AggrApp a <$> childT AppE1Arg (toAggregateExprT x)
        case M.lookup agg aggMap of
            Just (gaIdx, gaName) -> do
                pure $ inject $ P.tupElem gaIdx (Var (TupleT groupElemTy) gaName)
            Nothing    -> do
                gaName <- liftstateT $ freshNameT []
                let gaElemTy = TupleT $ groupElemTy ++ [aggTy]
                constT $ put $ Just (gaName, agg)
                pure $ inject $ P.tupElem (nextGaIdx groupElemTy) (Var gaElemTy gaName)
    ExprCL (Let _ x' _ _)
        | x == x'   -> childR LetBind (searchAggExpR groupElemTy aggMap x)
        | otherwise -> childR LetBind (searchAggExpR groupElemTy aggMap x)
                       <+
                       childR LetBody (searchAggExpR groupElemTy aggMap x)
    ExprCL Comp{} -> childR CompQuals (searchAggQualsR groupElemTy aggMap x)
    ExprCL _ -> oneR $ searchAggExpR groupElemTy aggMap x
    _ -> fail "only expressions"

-- | Search qualifiers for a matching aggregate. Replace aggregate on the spot.
searchAggQualsR :: [Type] -> AggrMap -> Ident -> Rewrite CompCtx GroupM CL
searchAggQualsR groupElemTy aggMap x = readerT $ \cl -> case cl of
    QualsCL (BindQ x' _ :* _)
        | x == x' ->
            pathR [QualsHead, BindQualExpr] $ searchAggExpR groupElemTy aggMap x
        | otherwise ->
            pathR [QualsHead, BindQualExpr] $ searchAggExpR groupElemTy aggMap x
            <+
            childR QualsTail (searchAggQualsR groupElemTy aggMap x)
    QualsCL (S BindQ{}) ->
        pathR [QualsSingleton, BindQualExpr] $ searchAggExpR groupElemTy aggMap x
    QualsCL (GuardQ _ :* _) ->
        pathR [QualsHead, GuardQualExpr] $ searchAggExpR groupElemTy aggMap x
        <+
        childR QualsTail (searchAggQualsR groupElemTy aggMap x)
    QualsCL (S (GuardQ _)) ->
        pathR [QualsSingleton, GuardQualExpr] $ searchAggExpR groupElemTy aggMap x
    _ -> fail "qualifiers only"
