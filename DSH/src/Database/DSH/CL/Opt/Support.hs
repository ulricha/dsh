{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE LambdaCase     #-}
    
-- | Support rewrites (partial evaluation, house cleaning)
module Database.DSH.CL.Opt.Support
  ( factorConstantPredsR
  ) where
  
import Debug.Trace

import           Control.Applicative
import           Control.Arrow

import           Database.DSH.CL.Lang
import           Database.DSH.CL.Kure
import qualified Database.DSH.CL.Primitives as P
import           Database.DSH.CL.Opt.Aux

--------------------------------------------------------------------------------
-- Factoring out complex expressions from comprehension qualifiers

-- TODO
-- better name
-- do the same for comprehension heads



complexPathT :: TranslateC CL [(Expr, PathC)]
complexPathT = do
    ExprCL e <- idR
    -- debugPretty "complexPathT" e
    path <- snocPathToPath <$> absPathT
    let ret = return [(e, path)]
    case e of
        Comp _ _ _                                 -> trace "comp" ret
        If _ _ _ _                                 -> trace "if" ret
        AppE2 _ (Prim2 op _) _ _ | complexPrim2 op -> trace "app2" ret
        AppE1 _ (Prim1 op _) _   | complexPrim1 op -> trace "app1" ret
        _ -> fail "not a complex expression"

factorR :: TranslateC CL (Ident, Expr, Expr)
factorR = do
    -- Collect largest complex expressions in all childs
    candidateExprs <- allT $ onetdT complexPathT
    debugPretty "collected" candidateExprs
    
    (complexExpr, complexPath) : _ <- return $ filter (null . freeVars . fst) candidateExprs
    
    debugMsg "carnary1"
    x                          <- freshNameT []
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
factorQualR =
    readerT $ \case
        GuardQ p :* qs -> do
            (x, xs, p') <- constT (return $ inject $ p) >>> factorR
            return $ BindQ x xs :* GuardQ p' :* qs
        S (GuardQ p) -> do
            (x, xs, p') <- constT (return $ inject $ p) >>> factorR
            return $ BindQ x xs :* (S $ GuardQ p')
        _ -> fail "no match"

factorConstantPredsR :: RewriteC CL
factorConstantPredsR = do
    Comp t h qs <- promoteT idR
    qs' <- constT (return qs) >>> onetdR factorQualR
    return $ inject $ Comp t h qs'
    
