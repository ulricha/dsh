{-# LANGUAGE TemplateHaskell #-}

-- | Introduce GroupAggr operators for combinations of group and aggregation
-- operators. This effectively fuses group creation and aggregation and avoids
-- materialization of the groups.
module Database.DSH.CL.Opt.GroupAggr
  ( groupaggR
  ) where

import           Control.Arrow
import           Data.Semigroup                 ((<>))

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
groupaggR = mergegroupaggR <+ extendgroupaggR

--------------------------------------------------------------------------------

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

mkGroupAggr :: AggrApp -> Expr -> (Expr, Type)
mkGroupAggr agg xs = (GroupAggP (ListT resTy) (pure agg) xs, resTy)
  where
    aTy   = aggType agg
    resTy = TupleT [gTy, ListT eTy, aTy]
    (eTy, gTy) = case typeOf xs of
            ListT (TupleT [ty1, ty2]) -> (ty1, ty2)
            _                         -> error "groupaggR: type mismatch"

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
