{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}

-- | Introduce simple theta joins
module Database.DSH.CL.Opt.FlatJoin
    ( flatjoinsR
    ) where

import           Control.Arrow
import qualified Data.Map                      as M
import qualified Data.Set                      as S

import           Database.DSH.Common.Kure
import           Database.DSH.CL.Kure
import           Database.DSH.CL.Lang
import           Database.DSH.CL.Opt.Auxiliary

import           Database.DSH.CL.Opt.AntiJoin
import           Database.DSH.CL.Opt.SemiJoin
import           Database.DSH.CL.Opt.ThetaJoin

------------------------------------------------------------------------
-- Flat join detection

-- | Try to build a join from a list of generators and a single
-- guard. If we can build a theta join, the remaining predicates must
-- be tuplified. For this reason, we pass them in here.
mkFlatJoin :: MergeGuard
mkFlatJoin comp guard guardsToTry leftOverGuards = do
    let C ty h qs = comp
    env <- S.fromList . M.keys . clBindings <$> contextT
    let comp' = ExprCL $ Comp ty h (insertGuard guard env qs)
    tryAntijoinR comp' <+ trySemijoinR comp' <+ tryThetajoinR comp'

  where
    tryAntijoinR :: CL -> TransformC () (Comp, [Expr], [Expr])
    tryAntijoinR comp' = do
        ExprCL (Comp ty h qs') <- constT (return comp') >>> antijoinR
        return (C ty h qs', guardsToTry, leftOverGuards)

    trySemijoinR :: CL -> TransformC () (Comp, [Expr], [Expr])
    trySemijoinR comp' = do
        ExprCL (Comp ty h qs') <- constT (return comp') >>> semijoinR
        return (C ty h qs', guardsToTry, leftOverGuards)

    tryThetajoinR :: CL -> TransformC () (Comp, [Expr], [Expr])
    tryThetajoinR comp' = do
        res <- constT (return comp') >>> thetajoinR guardsToTry leftOverGuards
        (ExprCL (Comp ty h qs), guardsToTry', leftOverGuards') <- return res
        return (C ty h qs, guardsToTry', leftOverGuards')

flatjoinsR :: RewriteC CL
flatjoinsR = logR "flatjoin" $ mergeGuardsIterR mkFlatJoin

