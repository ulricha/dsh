{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE TemplateHaskell     #-}
    
-- | Extract loop-invariant "complex" expressions from comprehension guards
module Database.DSH.CL.Opt.LoopInvariant
  ( loopInvariantGuardR
  ) where

import Debug.Trace
import Text.Printf
  
import           Control.Applicative
import           Control.Arrow
import           Data.Maybe
import           Data.List

import           Database.DSH.Common.Pretty
import           Database.DSH.Common.Lang
import           Database.DSH.Common.Kure
import           Database.DSH.CL.Lang
import           Database.DSH.CL.Kure
import qualified Database.DSH.CL.Primitives as P
import           Database.DSH.CL.Opt.Aux

traverseT :: [Ident] -> TransformC CL (Expr, PathC)
traverseT localVars = readerT $ \expr -> trace (printf "traverseT at %s" (pp expr)) $! case expr of
    -- We do not traverse into lambdas and comprehensions which are
    -- nested in our current comprehension.  
    -- 
    -- FIXME technically, we could consider the generators of the
    -- nested comprehension.
    ExprCL (Comp _ _ _) -> fail "we don't traverse into comprehensions"
    ExprCL (Lam _ _ _)  -> fail "we don't traverse into lambdas"

    -- We do not traverse into the mapping argument of higher-order
    -- list combinators
    ExprCL (AppE2 _ (Prim2 Map _) _ _)          -> childT AppE2Arg2 $ searchInvariantExprT localVars
    ExprCL (AppE2 _ (Prim2 ConcatMap _) _ _)    -> childT AppE2Arg2 $ searchInvariantExprT localVars
    ExprCL (AppE2 _ (Prim2 Filter _) _ _)       -> childT AppE2Arg2 $ searchInvariantExprT localVars
    ExprCL (AppE2 _ (Prim2 GroupWithKey _) _ _) -> childT AppE2Arg2 $ searchInvariantExprT localVars
    ExprCL (AppE2 _ (Prim2 SortWith _) _ _)     -> childT AppE2Arg2 $ searchInvariantExprT localVars

    ExprCL _                                     -> oneT $ searchInvariantExprT localVars
    _                                            -> fail "we only consider expressions"

-- | Collect a path to a complex expression
complexPathT :: [Ident] -> TransformC CL (Expr, PathC)
complexPathT localVars = do
    ExprCL e <- idR
    -- debugPretty "complexPathT" e
    path <- snocPathToPath <$> absPathT
    debugPretty "complexPathT" e
    
    -- We are only interested in constant expressions that do not
    -- depend on variables bound by generators in the enclosing
    -- comprehension.
    debugMsg $ "free: " ++ pp (freeVars e)
    guardM $ null $ freeVars e `intersect` localVars

    -- FIXME more precise heuristics could be employed: A
    -- comprehension is only "complex" if it has more than one
    -- generator OR a filter OR something complex in the head.
    case e of
        Comp _ _ _                                 -> return (e, path)
        If _ _ _ _                                 -> return (e, path)
        AppE2 _ (Prim2 op _) _ _ | complexPrim2 op -> return (e, path)
        AppE1 _ (Prim1 op _) _   | complexPrim1 op -> return (e, path)
        _ -> fail "not a complex expression"

-- | Traverse expressions top-down, searching for loop-invariant
-- complex expressions.
searchInvariantExprT :: [Ident] -> TransformC CL (Expr, PathC)
searchInvariantExprT localVars = complexPathT localVars <+ (promoteT $ traverseT localVars)


-- | In a given guard expression, search for a complex loop-invariant
-- sub-expression and move it to a generator.
invariantExprT :: [Ident] -> TransformC CL (Ident, Expr, Expr)
invariantExprT localVars = do
    -- Collect largest complex expression in all childs
    debugMsg $ "start collection"
    (complexExpr, complexPath) <- oneT $ searchInvariantExprT localVars

    debugMsg $ "invariantExprT " ++ pp complexExpr

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
    readerT $ \q -> case q of
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
    debugMsg $ "loopInvariantGuardR " ++ show genVars
    debugMsg $ "CC\n" ++ pp (Comp t h qs)
    qs' <- constT (return qs) >>> onetdR (invariantQualR genVars)
    return $ inject $ Comp t h qs'
