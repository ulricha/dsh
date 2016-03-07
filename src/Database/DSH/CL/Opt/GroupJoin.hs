{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Database.DSH.CL.Opt.GroupJoin
  ( groupjoinR
  ) where

import           Debug.Trace

import           Control.Arrow
import           Control.Monad

import           Data.List
import qualified Data.Set as S
import qualified Data.Map as M
import qualified Data.List.NonEmpty as N

import           Database.DSH.Common.Lang
import           Database.DSH.Common.Nat
import           Database.DSH.Common.Pretty

import           Database.DSH.CL.Lang
import           Database.DSH.CL.Kure

import qualified Database.DSH.CL.Primitives as P

import           Database.DSH.CL.Opt.Auxiliary
import           Database.DSH.CL.Opt.CompNormalization


-- | Rewrite the child expression of the aggregate into a scalar expression. The
-- identifier 'x' is the name bound by the outer comprehension.
--
-- The following forms can be rewritten:
--
-- @ x.2 @
-- @ [ f y | y <- x.2 ] @
toAggregateExprT :: Ident -> TransformC CL ScalarExpr
toAggregateExprT x =
    readerT $ \e -> case e of
        ExprCL (Comp _ _ (S (BindQ y (TupSecondP _ (Var _ x'))))) | x == x' ->
            childT CompHead $ promoteT (toScalarExpr y)
        ExprCL (TupSecondP t (Var _ x')) | x == x'                          ->
            return $ JInput t
        _                                                                   ->
            fail "not an aggregate expression"

-- | Traverse though an expression and search for an aggregate that is eligible
-- for being merged into a NestJoin.
searchAggregatedGroupT :: Ident -> TransformC CL (PathC, Aggregate, ScalarExpr)
searchAggregatedGroupT x =
    readerT $ \e -> case e of
        ExprCL (AppE1 _ (Agg agg) e) ->
            (,,) <$> (snocPathToPath <$> absPathT)
                 <*> pure agg
                 <*> childT AppE1Arg (toAggregateExprT x)
        ExprCL _      -> oneT $ searchAggregatedGroupT x
        _             -> fail "only traverse through expressions"

--------------------------------------------------------------------------------

aggType :: Aggregate -> Type -> Type
aggType Length _   = PIntT
aggType Sum ty     = ty
aggType Maximum ty = ty
aggType Minimum ty = ty
aggType Avg ty     = ty
aggType And _      = PBoolT
aggType Or _       = PBoolT

groupjoinR :: RewriteC CL
groupjoinR = do
    e@(Comp ty h (S (BindQ x (NestJoinP _ p xs ys)))) <- promoteT idR

    -- Search for an aggregate applied to the groups that are produced by
    -- NestJoin.
    (aggPath, agg, aggExpr) <- searchAggregatedGroupT x
    headPath <- drop 1 <$> localizePathT aggPath

    -- Type of the GroupJoin result: xs :: [a], ys :: [b] => [(a, p(b))]
    let xt  = elemT $ typeOf xs
        at  = aggType agg $ elemT $ typeOf ys
        ty' = ListT (TupleT [xt, at])
        xv' = Var ty' x
    let joinOp = AppE2 ty' (GroupJoin p agg aggExpr) xs ys

    -- In the head expression, update the type of the generator variable. Then,
    -- replace the aggregate with a reference to the aggregate computed by the
    -- GroupJoin.
    h' <- constT (return $ inject h)
              >>> substR x xv'
              >>> pathR headPath (constT $ return $ inject $ P.snd xv')
              >>> projectT
    return $ inject $ Comp ty h' (S (BindQ x joinOp))
