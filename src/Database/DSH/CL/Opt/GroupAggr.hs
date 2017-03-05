{-# LANGUAGE TemplateHaskell #-}

-- | Introduce GroupAggr operators for combinations of group and aggregation
-- operators. This effectively fuses group creation and aggregation and avoids
-- materialization of the groups.
module Database.DSH.CL.Opt.GroupAggr
  ( groupaggR
  ) where

import           Control.Arrow
import           Data.Semigroup                 ((<>))
import qualified Data.Set                       as S
import qualified Data.Map                       as M

import           Database.DSH.Common.Impossible
import           Database.DSH.Common.Kure
import           Database.DSH.Common.Lang
import           Database.DSH.Common.Nat

import           Database.DSH.CL.Kure
import           Database.DSH.CL.Lang

import qualified Database.DSH.CL.Primitives     as P

import           Database.DSH.CL.Opt.Auxiliary

-- | Fold/Group Fusion
groupaggR :: RewriteC CL
-- groupaggR = mergegroupaggR <+ extendgroupaggR
groupaggR = mergegroupaggHeadR <+ mergegroupaggQualsR

--------------------------------------------------------------------------------

type GroupM = RewriteStateM (Maybe (Ident, AggrApp)) RewriteLog

mergegroupaggHeadR :: RewriteC CL
mergegroupaggHeadR = logR " groupagg.construct.head" $ do
    Comp ty h _ <- promoteT idR
    (qs', h') <- childT CompQuals $ searchGroupSpineHeadT h
    pure $ inject $ Comp ty h' qs'

gaSubst :: Expr -> Expr
gaSubst gaVar = P.pair (P.fst gaVar) (P.snd gaVar)

-- | Traverse qualifiers from the current candidate generator to the end. Once
-- reaching the end, traverse the head searching for an aggregate that matches
-- the candidate generator.
traverseToHeadT :: [Type] -> TupleIndex -> Ident -> Expr -> Transform CompCtx GroupM CL Expr
traverseToHeadT groupElemTy nextGaIdx x h = readerT $ \qs -> case qs of
    QualsCL (BindQ x' _ :* _)
        | x == x'   -> fail "shadowing"
        | otherwise -> childT QualsTail $ traverseToHeadT groupElemTy nextGaIdx x h
    QualsCL (GuardQ _ :* _) -> childT QualsTail $ traverseToHeadT groupElemTy nextGaIdx x h
    QualsCL (S (BindQ x' xs))
        | x == x'   -> fail "shadowing"
        | otherwise -> do
            ctx <- contextT
            let ctx' = ctx { clBindings = M.insert x' (elemT $ typeOf xs) (clBindings ctx) }
            constT (pure $ inject h) >>> withContextT ctx' (searchAggExpR groupElemTy nextGaIdx x) >>> projectT
    QualsCL (S (GuardQ _)) -> do
        constT (pure $ inject h) >>> searchAggExpR groupElemTy nextGaIdx x >>> projectT
    _ -> fail "no qualifiers"

searchAggExpR :: [Type] -> TupleIndex -> Ident -> Rewrite CompCtx GroupM CL
searchAggExpR groupElemTy nextGaIdx x = readerT $ \cl -> case cl of
    ExprCL (AppE1 aggTy (Agg a) _) -> do
        agg <- AggrApp a <$> childT AppE1Arg (toAggregateExprT x)
        gaName <- liftstateT $ freshNameT []
        let gaElemTy = TupleT $ groupElemTy ++ [aggTy]
        constT $ put $ Just (gaName, agg)
        pure $ inject $ P.tupElem nextGaIdx (Var gaElemTy gaName)
    ExprCL (Let _ x' _ _)
        | x == x'   -> childR LetBind (searchAggExpR groupElemTy nextGaIdx x)
        | otherwise -> childR LetBind (searchAggExpR groupElemTy nextGaIdx x)
                       <+
                       childR LetBody (searchAggExpR groupElemTy nextGaIdx x)
    ExprCL Comp{} -> childR CompQuals (searchAggQualsR groupElemTy nextGaIdx x)
    ExprCL _ -> oneR $ searchAggExpR groupElemTy nextGaIdx x
    _ -> fail "only expressions"

searchAggQualsR :: [Type] -> TupleIndex -> Ident -> Rewrite CompCtx GroupM CL
searchAggQualsR groupElemTy nextGaIdx x = readerT $ \cl -> case cl of
    QualsCL (BindQ x' _ :* _)
        | x == x' ->
            pathR [QualsHead, BindQualExpr] $ searchAggExpR groupElemTy nextGaIdx x
        | otherwise ->
            pathR [QualsHead, BindQualExpr] $ searchAggExpR groupElemTy nextGaIdx x
            <+
            childR QualsTail (searchAggQualsR groupElemTy nextGaIdx x)
    QualsCL (S BindQ{}) ->
        pathR [QualsSingleton, BindQualExpr] $ searchAggExpR groupElemTy nextGaIdx x
    QualsCL (GuardQ _ :* _) ->
        pathR [QualsHead, GuardQualExpr] $ searchAggExpR groupElemTy nextGaIdx x
        <+
        childR QualsTail (searchAggQualsR groupElemTy nextGaIdx x)
    QualsCL (S (GuardQ _)) ->
        pathR [QualsSingleton, GuardQualExpr] $ searchAggExpR groupElemTy nextGaIdx x
    _ -> fail "qualifiers only"

mergeGroupQualsT :: Expr -> Ident -> Expr -> TransformC CL (NL Qual, Expr)
mergeGroupQualsT h x xs = do
    (Just (gaName, agg), qsCl) <- statefulT Nothing
                                      $ childT QualsTail
                                      $ searchAggQualsR (mkGroupElemTy $ typeOf xs) 3 x
    let (gaOp, gaElemTy) = mkGroupAggr agg xs
    scopeNames <- S.insert x <$> inScopeNamesT
    qs' <- constT $ projectM qsCl
    let (qs'', h') = substCompE scopeNames x (gaSubst $ Var gaElemTy gaName) qs' h
    pure (BindQ gaName gaOp :* qs'', h')

searchGroupSpineHeadT :: Expr -> TransformC CL (NL Qual, Expr)
searchGroupSpineHeadT h = readerT $ \cl -> case cl of
    QualsCL (BindQ x (GroupP ty xs) :* qs) ->
        do
            (Just (gaName, agg), h') <- statefulT Nothing
                                            $ childT QualsTail
                                            $ traverseToHeadT (mkGroupElemTy $ typeOf xs) 3 x h
            let (gaOp, gaElemTy) = mkGroupAggr agg xs
            scopeNames <- S.insert x <$> inScopeNamesT
            let (qs', h'') = substCompE scopeNames x (gaSubst $ Var gaElemTy gaName) qs h'
            pure (BindQ gaName gaOp :* qs', h'')
        <+
        do
            (qs', h') <- childT QualsTail (searchGroupSpineHeadT h)
            pure (BindQ x (GroupP ty xs) :* qs', h')
    QualsCL (S (BindQ x (GroupP _ xs))) -> do
        ctx <- contextT
        let ctx' = ctx { clBindings = M.insert x (elemT $ typeOf xs) (clBindings ctx) }
        (Just (gaName, agg), h') <- statefulT Nothing
                                        $ constT (pure $ inject h)
                                              >>> withContextT ctx' (searchAggExpR (mkGroupElemTy $ typeOf xs) 3 x)
                                              >>> projectT
        let (gaOp, gaElemTy) = mkGroupAggr agg xs
        scopeNames <- S.insert x <$> inScopeNamesT
        let h'' = substE scopeNames x (gaSubst $ Var gaElemTy gaName) h'
        pure (S (BindQ gaName gaOp), h'')
    QualsCL (BindQ x xs :* _)             -> do
        (qs', h') <- childT QualsTail (searchGroupSpineQualsT h)
        pure (BindQ x xs :* qs', h')
    QualsCL (GuardQ p :* _)               -> do
        (qs', h') <- childT QualsTail (searchGroupSpineQualsT h)
        pure (GuardQ p :* qs', h')
    _                                     -> fail "no match"

searchGroupSpineQualsT :: Expr -> TransformC CL (NL Qual, Expr)
searchGroupSpineQualsT h = readerT $ \cl -> case cl of
    QualsCL (BindQ x (GroupP ty xs) :* _) ->
        mergeGroupQualsT h x xs
        <+
        do
            (qs', h') <- childT QualsTail (searchGroupSpineQualsT h)
            pure (BindQ x (GroupP ty xs) :* qs', h')
    QualsCL (BindQ x xs :* _)             -> do
        (qs', h') <- childT QualsTail (searchGroupSpineQualsT h)
        pure (BindQ x xs :* qs', h')
    QualsCL (GuardQ p :* _)               -> do
        (qs', h') <- childT QualsTail (searchGroupSpineQualsT h)
        pure (GuardQ p :* qs', h')
    _                                     -> fail "no match"

mergegroupaggQualsR :: RewriteC CL
mergegroupaggQualsR = logR " groupagg.construct.quals" $ do
    Comp ty h _ <- promoteT idR
    (qs', h') <- childT CompQuals $ searchGroupSpineQualsT h
    pure $ inject $ Comp ty h' qs'

-- | Introduce a new groupaggr operator by merging one particular aggregate into
-- a group operator.
mergegroupaggR :: RewriteC CL
mergegroupaggR = logR "groupagg.construct" $ do
    Comp ty _ qs <- promoteT idR
    -- We need one group generator on a comprehension
    (x, xs) <- case qs of
        S (BindQ x (GroupP _ xs))  -> pure (x, xs)
        BindQ x (GroupP _ xs) :* _ -> pure (x, xs)
        _                          -> fail "no match"

    -- Search for an eligible aggregate in the comprehension head and guards.
    (aggPath, agg) <- childT CompHead (searchAggregatedGroupT x)
                      <+
                      pathT [CompQuals, QualsTail] (traverseGuardsT x (searchAggregatedGroupT x))

    let (gaOp, gaTy) = mkGroupAggr agg xs
        xv'          = Var gaTy x

    localPath <- localizePathT aggPath

    -- Replace the aggregate expression with x.3 (the aggregate produced by
    -- groupaggr).
    Comp _ h' qs' <- pathR localPath (constT $ return $ inject $ P.third xv') >>> projectT

    -- Update the type of the variable bound by the GroupAggr generator.
    scopeNames <- inScopeNamesT
    let (qs'', h'') = substCompE scopeNames x xv' qs' h'

    case qs'' of
        BindQ _ _ :* qsr -> pure $ inject $ Comp ty h'' (BindQ x gaOp :* qsr)
        S (BindQ _ _)    -> pure $ inject $ Comp ty h'' (S (BindQ x gaOp))
        _                -> $impossible

mkGroupElemTy :: Type -> [Type]
mkGroupElemTy ty = case ty of
    ListT (TupleT [eTy, gTy]) -> [gTy, ListT eTy]
    _ -> error "groupElemTy: type mismatch"

mkGroupAggr :: AggrApp -> Expr -> (Expr, Type)
mkGroupAggr agg xs = (GroupAggP (ListT resTy) (pure agg) xs, resTy)
  where
    aTy   = aggType agg
    resTy = TupleT $ mkGroupElemTy (typeOf xs) ++ [aTy]

--------------------------------------------------------------------------------

-- | Extend one aggregate by merging it into an existing groupaggr operator.
extendgroupaggR :: RewriteC CL
extendgroupaggR = logR "groupagg.extend" $ do
    Comp ty _ qs <- promoteT idR

    -- We need one group generator on a comprehension
    (resTy, x, as, xs) <- case qs of
        S (BindQ x (GroupAggP resTy as xs))  -> pure (resTy, x, as, xs)
        BindQ x (GroupAggP resTy as xs) :* _ -> pure (resTy, x, as, xs)
        _                                    -> fail "no match"

    -- Search for an eligible aggregate in the comprehension head and guards.
    (aggPath, newAgg) <- childT CompHead (searchAggregatedGroupT x)
                         <+
                         pathT [CompQuals, QualsTail] (traverseGuardsT x (searchAggregatedGroupT x))

    let (gaOp, gaTy) = extendGroupAggr resTy newAgg as xs
        xv'          = Var gaTy x

    localPath <- localizePathT aggPath


    -- Replace the aggregate expression with the corresponding tuple index in
    -- the groupaggr output. The offset is computed based on the grouping key,
    -- the groups and all pre-existing aggregates).
    let newAggIdx = intIndex (1 + 1 + length as + 1)
    Comp _ h' qs' <- pathR localPath (constT $ return $ inject $ P.tupElem newAggIdx xv') >>> projectT

    -- Update the type of the variable bound by the GroupAggr generator.
    scopeNames <- inScopeNamesT
    let (qs'', h'') = substCompE scopeNames x xv' qs' h'

    case qs'' of
        BindQ _ _ :* qsr -> pure $ inject $ Comp ty h'' (BindQ x gaOp :* qsr)
        S (BindQ _ _)    -> pure $ inject $ Comp ty h'' (S (BindQ x gaOp))
        _                -> $impossible

extendGroupAggr :: Type -> AggrApp -> NE AggrApp -> Expr -> (Expr, Type)
extendGroupAggr resTy newAgg aggs xs = (GroupAggP (ListT gaTy) (aggs <> pure newAgg) xs, gaTy)
  where
    aTy  = aggType newAgg
    gaTy = case resTy of
        ListT (TupleT tys) -> TupleT $ tys ++ pure aTy
        _                  -> error "extendGroupAggr: type mismatch"
