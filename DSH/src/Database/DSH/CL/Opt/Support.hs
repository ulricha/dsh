{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE TemplateHaskell     #-}
    
-- | Support rewrites (partial evaluation, house cleaning)
module Database.DSH.CL.Opt.Support
  ( houseCleaningR
  , partialEvalR
  , algebraicRewritesR
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

------------------------------------------------------------------
-- Simple housecleaning support rewrites.
    
-- | Eliminate a map with an identity body
-- map (\x -> x) xs => xs
identityMapR :: RewriteC Expr
identityMapR = do
    AppE2 _ (Prim2 Map _) (Lam _ x (Var _ x')) xs <- idR
    guardM $ x == x'
    return xs
    
-- | Eliminate a comprehension with an identity head
-- [ x | x <- xs ] => xs
identityCompR :: RewriteC Expr
identityCompR = do
    Comp _ (Var _ x) (S (BindQ x' xs)) <- idR
    guardM $ x == x'
    return xs
    
-- | Eliminate tuple construction if the elements are first and second of the
-- same tuple:
-- pair (fst x) (snd x) => x
pairR :: RewriteC Expr
pairR = do
    AppE2 _ (Prim2 Pair _) (AppE1 _ (Prim1 Fst _) v@(Var _ x)) (AppE1 _ (Prim1 Snd _) (Var _ x')) <- idR
    guardM $ x == x'
    return v
    
-- | Merge two filters stacked on top of each other.
mergeFilterR :: RewriteC Expr
mergeFilterR = do
    AppE2 _ (Prim2 Filter _) 
            (Lam _ x1 p1)
            (AppE2 _ (Prim2 Filter _)
                     (Lam _ x2 p2)
                     xs)                <- idR

    let xt = elemT $ typeOf xs
                     
    p2' <- (constT $ return $ inject p2) >>> substR x2 (Var xt x1) >>> projectT
    
    let p' = BinOp (xt .-> boolT) Conj p1 p2'
    
    return $ P.filter (Lam (xt .-> boolT) x1 p') xs
    
houseCleaningR :: RewriteC CL
houseCleaningR = promoteR $ (identityMapR >>> debugTrace "identityMap")
                            <+ (identityCompR >>> debugTrace "identityCompR")
                            <+ (pairR >>> debugTrace "pair")
                            <+ (mergeFilterR >>> debugTrace "mergefilter")
               
--------------------------------------------------------------------------------
-- Partial evaluation rules

fstR :: RewriteC Expr
fstR = do
    AppE1 _ (Prim1 Fst _) (AppE2 _ (Prim2 Pair _) e1 _) <- idR
    return e1

sndR :: RewriteC Expr
sndR = do
    AppE1 _ (Prim1 Snd _) (AppE2 _ (Prim2 Pair _) _ e2) <- idR
    return e2
    
partialEvalR :: RewriteC CL
partialEvalR = promoteR (fstR >>> debugTrace "fst")
               <+ promoteR (sndR >>> debugTrace "snd")


--------------------------------------------------------------------------------
-- Rewrite rules for algebraic operators

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
            p' <- constT (return $ inject p) >>> anybuR (unpairFstR x) >>> projectT
            let lt' = xst .-> BoolT
            return $ inject $ AppE2 tj j (P.filter (Lam lt' x p') xs) ys
        else do
            p' <- constT (return $ inject p) >>> anybuR (unpairSndR x) >>> projectT
            let lt' = yst .-> BoolT
            return $ inject $ AppE2 tj j xs (P.filter (Lam lt' x p') ys) 

algebraicRewritesR :: RewriteC CL
algebraicRewritesR = filterThroughEquiJoinR
            

