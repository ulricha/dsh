{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE LambdaCase     #-}
    
-- | Support rewrites (partial evaluation, house cleaning)
module Database.DSH.CL.Opt.Support
  ( houseCleaningR
  , partialEvalR
  , factorConstantPredsR
  ) where
  
import Debug.Trace

import           Control.Applicative
import           Control.Arrow
import           Control.Monad

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
    
houseCleaningR :: RewriteC CL
houseCleaningR = promoteR $ (identityMapR >>> debugTrace "identityMap")
                            <+ (identityCompR >>> debugTrace "identityCompR")
                            <+ (pairR >>> debugTrace "pair")
               
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
-- 

complexPrim2 :: Prim2Op -> Bool
complexPrim2 op = 
    case op of
        Map       -> False
        ConcatMap -> False
        Pair      -> False
        _         -> True

complexPrim1 :: Prim1Op -> Bool
complexPrim1 op =
    case op of
        Concat -> False
        Fst    -> False
        Snd    -> False
        _      -> True

complexPathT :: TranslateC CL [(Expr, PathC)]
complexPathT = do
    ExprCL e <- idR
    debugPretty "complexPathT" e
    path <- snocPathToPath <$> absPathT
    let ret = return [(e, path)]
    case e of
        Comp _ _ _                                 -> trace "comp" ret
        If _ _ _ _                                 -> trace "if" ret
        AppE2 _ (Prim2 op _) _ _ | complexPrim2 op -> trace "app2" ret
        AppE1 _ (Prim1 op _) _   | complexPrim1 op -> trace "app1" ret
        e -> fail "not a complex expression"

factorR :: TranslateC CL (Ident, Expr, Expr)
factorR = do
    -- Collect largest complex expressions in all childs
    candidateExprs <- allT $ onetdT complexPathT
    debugPretty "collected" candidateExprs
    
    (complexExpr, complexPath) : _ <- return $ filter (null . freeVars . fst) candidateExprs
    
    debugMsg "carnary1"
    x                          <- freshNameT
    guardM $ null $ freeVars complexExpr
    debugMsg "carnary2"
    let complexType = typeOf complexExpr
    let singletonExpr = P.cons complexExpr (Lit (listT complexType) (ListV []))

    pathLen <- length <$> snocPathToPath <$> absPathT
    let localPath = drop pathLen complexPath

    let replacementExpr = constT $ return $ inject $ Var complexType x

    ExprCL simplifiedPred <- pathR localPath replacementExpr
    debugMsg "carnary3"

    return (x, singletonExpr, simplifiedPred)

factorQualR :: RewriteC (NL Qual)
factorQualR = do
    GuardQ pred :* qs <- idR
    (x, xs, pred) <- constT (return $ inject $ pred) >>> factorR
    return $ BindQ x xs :* GuardQ pred :* qs

factorQualEndR :: RewriteC (NL Qual)
factorQualEndR = do
    S (GuardQ pred) <- idR
    debugPretty "factorQualEndR" pred
    (x, xs, pred) <- constT (return $ inject $ pred) >>> factorR
    return $ BindQ x xs :* (S $ GuardQ pred)

factorConstantPredsR :: RewriteC CL
factorConstantPredsR = do
    Comp t h qs <- promoteT idR
    qs' <- constT (return qs) >>> onetdR (factorQualR <+ factorQualEndR)
    return $ inject $ Comp t h qs'
    
