{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE TemplateHaskell     #-}
    
-- | This module implements classic algebraic rewrites on the CL
-- algebra equivalents (filter, joins, ...).
module Database.DSH.CL.Opt.Algebraic
  ( algebraicRewritesR
  ) where
  
import Debug.Trace

import           Control.Applicative
import           Control.Arrow

import           Data.Maybe

import           Database.DSH.Common.Pretty
import           Database.DSH.CL.Lang
import           Database.DSH.CL.Kure
import qualified Database.DSH.CL.Primitives as P
import           Database.DSH.CL.Opt.Aux

algebraicRewritesR :: RewriteC CL
algebraicRewritesR = filterThroughEquiJoinR

-- FIXME: push filters through other join operators (semi, anti, nest)

--------------------------------------------------------------------------------
-- Push a filter through an equijoin or a cartesian product
-- FIXME: implement the product variant

-- | Return path to occurence of variable x
varPathT :: Ident -> TranslateC CL PathC
varPathT x = do
    ExprCL  (Var _ x') <- idR
    guardM $ x == x'
    snocPathToPath <$> absPathT

-- | Replace accesses to the first pair component of a given variable
-- by the variable itself.
unpairFstR :: Ident -> RewriteC CL
unpairFstR x = do
    ExprCL (AppE1 _ (Prim1 op' _) v@(Var (PairT t1 _) x')) <- idR
    guardM $ x == x'
    return $ ExprCL (Var t1 x)

-- | Replace accesses to the second pair component of a given variable
-- by the variable itself.
unpairSndR :: Ident -> RewriteC CL
unpairSndR x = do
    ExprCL (AppE1 _ (Prim1 op' _) v@(Var (PairT _ t2) x')) <- idR
    guardM $ x == x'
    return $ ExprCL (Var t2 x)

-- | Check if the expression parenting the given path is a tuple
-- accessor (fst/snd).
parentOpT :: PathC -> TranslateC CL (Maybe Prim1Op)
parentOpT path = do
    let parentPath = init path
    parentExpr <- pathT parentPath idR
    case parentExpr of
        ExprCL (AppE1 _ (Prim1 Fst _) _) -> return $ Just Fst
        ExprCL (AppE1 _ (Prim1 Snd _) _) -> return $ Just Snd
        e                                -> return Nothing

-- | Push a filter through an equijoin if the filter condition only
-- looks at one part of the tuples produced by the join.
filterThroughEquiJoinR :: RewriteC CL
filterThroughEquiJoinR = do
    -- filter (\x -> p) (xs ⨝ ys)
    ExprCL (AppE2 (ListT (PairT xst yst)) (Prim2 Filter _) (Lam _ x p) (AppE2 tj j@(Prim2 (EquiJoin _ _) _) xs ys)) <- idR

    varPaths <- childT AppE2Arg1 (collectT $ varPathT x)

    guardM $ not $ null varPaths

    parentPathLen <- length <$> snocPathToPath <$> absPathT

    -- Turn absolute paths to variables into paths relative to the
    -- current node.
    let localPaths = map (drop parentPathLen) varPaths

    varParentOps <- mapM parentOpT localPaths

    guardM $ all isJust varParentOps

    if all (maybe False (== Fst)) varParentOps
        then do
            p' <- constT (return $ inject p) >>> anytdR (unpairFstR x) >>> projectT
            let lt' = xst .-> BoolT
            return $ inject $ AppE2 tj j (P.filter (Lam lt' x p') xs) ys
        else do
            p' <- constT (return $ inject p) >>> anytdR (unpairSndR x) >>> projectT
            let lt' = yst .-> BoolT
            return $ inject $ AppE2 tj j xs (P.filter (Lam lt' x p') ys) 

            
