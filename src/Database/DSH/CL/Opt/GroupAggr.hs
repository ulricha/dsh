{-# LANGUAGE TemplateHaskell #-}

-- | Introduce GroupAggr operators for combinations of group and aggregation
-- operators. This effectively fuses group creation and aggregation and avoids
-- materialization of the groups.
module Database.DSH.CL.Opt.GroupAggr
    ( groupaggR
    ) where

import           Control.Arrow
import qualified Data.Map                      as M
import           Data.Semigroup                ((<>))
import qualified Data.Set                      as S

import           Database.DSH.Common.Kure
import           Database.DSH.Common.Lang

import           Database.DSH.CL.Kure
import           Database.DSH.CL.Lang

import           Database.DSH.CL.Opt.Auxiliary
import           Database.DSH.CL.Opt.FoldGroup

-- | Fold/Group Fusion
groupaggR :: RewriteC CL
groupaggR =    mergegroupaggHeadR
            <+ mergegroupaggQualsR
            <+ extendgroupaggHeadR
            <+ extendgroupaggQualsR

--------------------------------------------------------------------------------

mkGroupAggr :: AggrApp -> Expr -> (Expr, Type)
mkGroupAggr agg xs = (GroupAggP (ListT resTy) (pure agg) xs, resTy)
  where
    aTy   = aggType agg
    resTy = TupleT $ mkGroupElemTy (typeOf xs) ++ [aTy]

extendGroupAggr :: [Type] -> AggrApp -> NE AggrApp -> Expr -> (Expr, [Type])
extendGroupAggr gaElemTy newAgg aggs xs =
    ( GroupAggP (ListT $ TupleT gaElemTy') (aggs <> pure newAgg) xs
    , gaElemTy'
    )
  where
    aTy       = aggType newAgg
    gaElemTy' = gaElemTy ++ [aTy]

mkGroupElemTy :: Type -> [Type]
mkGroupElemTy ty = case ty of
    ListT (TupleT [eTy, gTy]) -> [gTy, ListT eTy]
    _                         -> error "groupElemTy: type mismatch"

--------------------------------------------------------------------------------
-- Initial Fold/Group fusion for aggregates in qualifiers

-- | Search qualifiers for a group generator that can be fused with aggregates
-- in subsequent qualifiers.
mergeGroupSpineQualsT :: Expr -> TransformC CL (NL Qual, Expr)
mergeGroupSpineQualsT h = readerT $ \cl -> case cl of
    QualsCL (BindQ x (GroupP ty xs) :* _) ->
        do
            let groupElemTy = mkGroupElemTy $ typeOf xs
            (Just (gaName, agg), qsCl) <- statefulT Nothing
                                              $ childT QualsTail
                                              $ searchAggQualsR groupElemTy M.empty x
            let (gaOp, gaElemTy) = mkGroupAggr agg xs
            scopeNames <- S.insert x <$> inScopeNamesT
            qs' <- constT $ projectM qsCl
            let (qs'', h') = substCompE scopeNames x (gaSubst (Var gaElemTy gaName) groupElemTy) qs' h
            pure (BindQ gaName gaOp :* qs'', h')
        <+
        do
            (qs', h') <- childT QualsTail (mergeGroupSpineQualsT h)
            pure (BindQ x (GroupP ty xs) :* qs', h')
    QualsCL (BindQ x xs :* _)             -> do
        (qs', h') <- childT QualsTail (mergeGroupSpineQualsT h)
        pure (BindQ x xs :* qs', h')
    QualsCL (GuardQ p :* _)               -> do
        (qs', h') <- childT QualsTail (mergeGroupSpineQualsT h)
        pure (GuardQ p :* qs', h')
    _                                     -> fail "no match"

-- | Introduce a new groupaggr operator by merging one particular aggregate from
-- the comprehension qualifiers into a group operator.
mergegroupaggQualsR :: RewriteC CL
mergegroupaggQualsR = logR "groupagg.construct.quals" $ do
    Comp ty h _ <- promoteT idR
    (qs', h') <- childT CompQuals $ mergeGroupSpineQualsT h
    pure $ inject $ Comp ty h' qs'

--------------------------------------------------------------------------------

-- | Search qualifiers for a group generator that can be fused with aggregates
-- in the head.
mergeGroupSpineHeadT :: Expr -> TransformC CL (NL Qual, Expr)
mergeGroupSpineHeadT h = readerT $ \cl -> case cl of
    QualsCL (BindQ x (GroupP ty xs) :* qs) ->
        do
            let groupElemTy = mkGroupElemTy $ typeOf xs
            (Just (gaName, agg), h') <- statefulT Nothing
                                            $ childT QualsTail
                                            $ traverseToHeadT groupElemTy M.empty x h
            let (gaOp, gaElemTy) = mkGroupAggr agg xs
            scopeNames <- S.insert x <$> inScopeNamesT
            let (qs', h'') = substCompE scopeNames x (gaSubst (Var gaElemTy gaName) groupElemTy) qs h'
            pure (BindQ gaName gaOp :* qs', h'')
        <+
        do
            (qs', h') <- childT QualsTail (mergeGroupSpineHeadT h)
            pure (BindQ x (GroupP ty xs) :* qs', h')
    QualsCL (S (BindQ x (GroupP _ xs))) -> do
        let groupElemTy = mkGroupElemTy $ typeOf xs
        ctx <- contextT
        let ctx' = ctx { clBindings = M.insert x (TupleT groupElemTy) (clBindings ctx) }
        (Just (gaName, agg), h') <- statefulT Nothing
                                        $ constT (pure $ inject h)
                                              >>> withContextT ctx' (searchAggExpR groupElemTy M.empty x)
                                              >>> projectT
        let (gaOp, gaElemTy) = mkGroupAggr agg xs
        scopeNames <- S.insert x <$> inScopeNamesT
        let h'' = substE scopeNames x (gaSubst (Var gaElemTy gaName) groupElemTy) h'
        pure (S (BindQ gaName gaOp), h'')
    QualsCL (BindQ x xs :* _)             -> do
        (qs', h') <- childT QualsTail (mergeGroupSpineHeadT h)
        pure (BindQ x xs :* qs', h')
    QualsCL (GuardQ p :* _)               -> do
        (qs', h') <- childT QualsTail (mergeGroupSpineHeadT h)
        pure (GuardQ p :* qs', h')
    _                                     -> fail "no match"

-- | Introduce a new groupaggr operator by merging one particular aggregate from
-- the comprehension head into a group operator.
mergegroupaggHeadR :: RewriteC CL
mergegroupaggHeadR = logR "groupagg.construct.head" $ do
    Comp ty h _ <- promoteT idR
    (qs', h') <- childT CompQuals $ mergeGroupSpineHeadT h
    pure $ inject $ Comp ty h' qs'

--------------------------------------------------------------------------------
-- Extension of groupaggr operators with additional aggregates.

-- | Search qualifiers for a groupaggr generator that can be extended with an
-- aggregate in the head.
extendGroupSpineHeadT :: Expr -> TransformC CL (NL Qual, Expr)
extendGroupSpineHeadT h = readerT $ \cl -> case cl of
    QualsCL (BindQ x (GroupAggP gaTy as xs) :* qs) ->
        do
            let gaElemTy = tupleElemTypes $ elemT gaTy
            (s, h') <- statefulT Nothing
                           $ childT QualsTail
                           $ traverseToHeadT gaElemTy (mkAggrMap x as) x h
            case s of
                Just (gaName, agg) -> do
                    let (gaOp, gaElemTy') = extendGroupAggr gaElemTy agg as xs
                    scopeNames <- S.insert x <$> inScopeNamesT
                    let gaVar = Var (TupleT gaElemTy') gaName
                    let (qs', h'') = substCompE scopeNames x (gaSubst gaVar gaElemTy) qs h'
                    pure (BindQ gaName gaOp :* qs', h'')
                Nothing -> pure (BindQ x (GroupAggP gaTy as xs) :* qs, h')
        <+
        do
            (qs', h') <- childT QualsTail (mergeGroupSpineHeadT h)
            pure (BindQ x (GroupAggP gaTy as xs) :* qs', h')
    QualsCL (S (BindQ x (GroupAggP gaTy as xs))) -> do
        let gaElemTy = tupleElemTypes $ elemT gaTy
        ctx <- contextT
        let ctx' = ctx { clBindings = M.insert x (TupleT gaElemTy) (clBindings ctx) }
        (s, h') <- statefulT Nothing
                       $ constT (pure $ inject h)
                             >>> withContextT ctx' (searchAggExpR gaElemTy (mkAggrMap x as)x)
                             >>> projectT
        case s of
            Just (gaName, agg) -> do
                let (gaOp, gaElemTy') = extendGroupAggr gaElemTy agg as xs
                scopeNames <- S.insert x <$> inScopeNamesT
                let gaVar = Var (TupleT gaElemTy') gaName
                let h'' = substE scopeNames x (gaSubst gaVar gaElemTy) h'
                pure (S (BindQ gaName gaOp), h'')
            Nothing -> pure (S (BindQ x (GroupAggP gaTy as xs)), h')
    QualsCL (BindQ x xs :* _)             -> do
        (qs', h') <- childT QualsTail (extendGroupSpineHeadT h)
        pure (BindQ x xs :* qs', h')
    QualsCL (GuardQ p :* _)               -> do
        (qs', h') <- childT QualsTail (extendGroupSpineHeadT h)
        pure (GuardQ p :* qs', h')
    _                                     -> fail "no match"

-- | Extend an existing groupaggr operator with one aggregate from the
-- comprehension head.
extendgroupaggHeadR :: RewriteC CL
extendgroupaggHeadR = logR "groupagg.extend.head" $ do
    Comp ty h _ <- promoteT idR
    (qs', h') <- childT CompQuals $ extendGroupSpineHeadT h
    pure $ inject $ Comp ty h' qs'

--------------------------------------------------------------------------------

-- | Search qualifiers for a groupaggr generator that can be extended with
-- aggregates in subsequent qualifiers.
extendGroupSpineQualsT :: Expr -> TransformC CL (NL Qual, Expr)
extendGroupSpineQualsT h = readerT $ \cl -> case cl of
    QualsCL (BindQ x (GroupAggP gaTy as xs) :* _) ->
        do
            let gaElemTy = tupleElemTypes $ elemT gaTy
            (s, qsCl) <- statefulT Nothing
                             $ childT QualsTail
                             $ searchAggQualsR gaElemTy (mkAggrMap x as) x
            qs' <- constT $ projectM qsCl
            case s of
                Just (gaName, agg) -> do
                    let (gaOp, gaElemTy') = extendGroupAggr gaElemTy agg as xs
                    scopeNames <- S.insert x <$> inScopeNamesT
                    let gaVar = Var (TupleT gaElemTy') gaName
                    let (qs'', h') = substCompE scopeNames x (gaSubst gaVar gaElemTy) qs' h
                    pure (BindQ gaName gaOp :* qs'', h')
                Nothing -> pure (BindQ x (GroupAggP gaTy as xs) :* qs', h)
        <+
        do
            (qs', h') <- childT QualsTail (extendGroupSpineQualsT h)
            pure (BindQ x (GroupAggP gaTy as xs) :* qs', h')
    QualsCL (BindQ x xs :* _)             -> do
        (qs', h') <- childT QualsTail (extendGroupSpineQualsT h)
        pure (BindQ x xs :* qs', h')
    QualsCL (GuardQ p :* _)               -> do
        (qs', h') <- childT QualsTail (extendGroupSpineQualsT h)
        pure (GuardQ p :* qs', h')
    _                                     -> fail "no match"

-- | Extend an existing groupaggr operator with one aggregate from the
-- comprehension qualifiers.
extendgroupaggQualsR :: RewriteC CL
extendgroupaggQualsR = logR "groupagg.extend.quals" $ do
    Comp ty h _ <- promoteT idR
    (qs', h') <- childT CompQuals $ extendGroupSpineQualsT h
    pure $ inject $ Comp ty h' qs'
