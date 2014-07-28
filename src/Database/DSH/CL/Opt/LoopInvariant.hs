{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE LambdaCase          #-}
    
-- | Extract loop-invariant "complex" expressions from comprehension guards
module Database.DSH.CL.Opt.LoopInvariant
  ( loopInvariantGuardR
  ) where
  
import           Control.Applicative
import           Control.Arrow
import           Data.Maybe
import           Data.List

import           Database.DSH.Common.Lang
import           Database.DSH.Common.Kure
import           Database.DSH.CL.Lang
import           Database.DSH.CL.Kure
import qualified Database.DSH.CL.Primitives as P
import           Database.DSH.CL.Opt.Aux

-- | Collect a path to a complex expression
complexPathT :: [Ident] -> TransformC CL [(Expr, PathC)]
complexPathT localVars = do
    ExprCL e <- idR
    -- debugPretty "complexPathT" e
    path <- snocPathToPath <$> absPathT
    debugPretty "complexPathT" e
    
    -- We are only interested in constant expressions that do not
    -- depend on variables bound by generators in the enclosing
    -- comprehension.
    guardM $ null $ freeVars e `intersect` localVars

    let ret = return [(e, path)]
    -- FIXME more precise heuristics could be employed: A
    -- comprehension is only "complex" if it has more than one
    -- generator OR a filter OR something complex in the head.
    case e of
        Comp _ _ _                                 -> ret
        If _ _ _ _                                 -> ret
        AppE2 _ (Prim2 op _) _ _ | complexPrim2 op -> ret
        AppE1 _ (Prim1 op _) _   | complexPrim1 op -> ret
        _ -> fail "not a complex expression"

-- | In a given guard expression, search for a complex loop-invariant
-- sub-expression and move it to a generator.
invariantExprT :: [Ident] -> TransformC CL (Ident, Expr, Expr)
invariantExprT localVars = do
    -- Collect largest complex expressions in all childs
    candidateExprs <- oneT $ onetdT (complexPathT localVars)

    -- choose the first candidate
    (complexExpr, complexPath) : _ <- return candidateExprs
    

    -- A fresh generator variable
    x                              <- freshNameT []

    -- The generator source for the loop-invariant expression
    let complexType = typeOf complexExpr
    let singletonExpr = P.cons complexExpr (Lit (listT complexType) (ListV []))

    -- Replace the loop-invariant expression with the fresh generator
    -- variable.
    pathLen <- length <$> snocPathToPath <$> absPathT
    let localPath = drop pathLen complexPath
    let replacementExpr = constT $ return $ inject $ Var complexType x
    ExprCL simplifiedPred <- pathR localPath replacementExpr

    return (x, singletonExpr, simplifiedPred)

invariantQualR :: [Ident] -> RewriteC (NL Qual)
invariantQualR localVars = do
    readerT $ \case
        GuardQ p :* qs -> do
            (x, xs, p') <- constT (return $ inject $ p) >>> (invariantExprT localVars)
            return $ BindQ x xs :* GuardQ p' :* qs
        S (GuardQ p) -> do
            (x, xs, p') <- constT (return $ inject $ p) >>> (invariantExprT localVars)
            return $ BindQ x xs :* (S $ GuardQ p')
        _ -> fail "no match"

loopInvariantGuardR :: RewriteC CL
loopInvariantGuardR = do
    Comp t h qs <- promoteT idR
    -- FIXME passing *all* generator variables in the current
    -- comprehension is too conservative. It would be sufficient to
    -- consider those preceding the guard that is under investigation.
    let genVars = fmap fst $ catMaybes $ fmap fromGen $ toList qs
    qs' <- constT (return qs) >>> onetdR (invariantQualR genVars)
    return $ inject $ Comp t h qs'
