{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE QuasiQuotes         #-}
{-# LANGUAGE TemplateHaskell     #-}

-- | Extract loop-invariant "complex" expressions from comprehensions
module Database.DSH.CL.Opt.LoopInvariant
  ( loopInvariantR
  ) where

import           Control.Applicative
import           Data.Maybe
import           Data.List

import           Database.DSH.Common.Impossible
import           Database.DSH.Common.Lang
import           Database.DSH.Common.Kure
import           Database.DSH.Common.Pretty
import           Database.DSH.CL.Lang
import           Database.DSH.CL.Kure
import qualified Database.DSH.CL.Primitives as P
import           Database.DSH.CL.Opt.Auxiliary

-- | Extract complex loop-invariant expressions from comprehension
-- heads and guards.
loopInvariantR :: RewriteC CL
loopInvariantR = loopInvariantGuardR <+ loopInvariantHeadR

--------------------------------------------------------------------------------
-- Common code for searching loop-invariant expressions

traverseT :: [Ident] -> TransformC CL (Expr, PathC)
traverseT localVars = readerT $ \expr -> case expr of
    -- We do not traverse into lambdas and comprehensions which are
    -- nested in our current comprehension.
    --
    -- FIXME technically, we could consider the generators of the
    -- nested comprehension.
    ExprCL (Comp _ _ _) -> fail "we don't traverse into comprehensions"

    ExprCL _                          -> oneT $ searchInvariantExprT localVars
    _                                 -> fail "we only consider expressions"

-- | Collect a path to a complex expression
complexPathT :: [Ident] -> TransformC CL (Expr, PathC)
complexPathT localVars = do
    ExprCL e <- idR
    -- debugPretty "complexPathT" e
    path <- snocPathToPath <$> absPathT

    -- We are only interested in constant expressions that do not
    -- depend on variables bound by generators in the enclosing
    -- comprehension.
    -- debugMsg $ "free: " ++ pp (freeVars e)
    guardM $ null $ freeVars e `intersect` localVars

    -- FIXME more precise heuristics could be employed: A
    -- comprehension is only "complex" if it has more than one
    -- generator OR a filter OR something complex in the head.
    case e of
        Comp _ _ _                          -> return (e, path)
        If _ _ _ _                          -> return (e, path)
        AppE2 _ op _ _ | complexPrim2 op    -> return (e, path)
        AppE1 _ op _   | complexPrim1 op    -> return (e, path)
        _ -> fail "not a complex expression"

-- | Traverse expressions top-down, searching for loop-invariant
-- complex expressions.
searchInvariantExprT :: [Ident] -> TransformC CL (Expr, PathC)
searchInvariantExprT localVars = complexPathT localVars <+ (promoteT $ traverseT localVars)

invariantQualR :: [Ident] -> TransformC CL (Expr, PathC)
invariantQualR localVars = readerT $ \expr -> case expr of
    QualsCL (BindQ{} :* _)  -> childT QualsTail (invariantQualR localVars)
    QualsCL (GuardQ _ :* _) -> (childT QualsHead (searchInvariantExprT localVars)
                                <+
                               childT QualsTail (invariantQualR localVars))
    QualsCL (S (GuardQ _))  -> pathT [QualsSingleton, GuardQualExpr] (searchInvariantExprT localVars)
    QualsCL (S BindQ{})     -> fail "no match"
    _                       -> $impossible

--------------------------------------------------------------------------------
-- Search and replace loop-invariant expressions

loopInvariantGuardR :: RewriteC CL
loopInvariantGuardR = do
    c@(Comp _ _ qs) <- promoteT idR
    -- FIXME passing *all* generator variables in the current
    -- comprehension is too conservative. It would be sufficient to
    -- consider those preceding the guard that is under investigation.
    let genVars = fmap fst $ catMaybes $ fmap fromGen $ toList qs
    (invExpr, invPath) <- childT CompQuals (invariantQualR genVars)
    letName            <- freshNameT (genVars ++ boundVars c)

    pathLen <- length <$> snocPathToPath <$> absPathT
    let localPath = drop pathLen invPath
        invVar    = Var (typeOf invExpr) letName

    ExprCL comp' <- pathR localPath (constT $ return $ inject invVar)
    return $ inject $ P.let_ letName invExpr comp'

loopInvariantHeadR :: RewriteC CL
loopInvariantHeadR = do
    Comp _ h qs <- promoteT idR
    let genVars = fmap fst $ catMaybes $ fmap fromGen $ toList qs
    (invExpr, invPath) <- childT CompHead (searchInvariantExprT genVars)
    letName            <- freshNameT (genVars ++ boundVars h)

    pathLen <- length <$> snocPathToPath <$> absPathT
    let localPath = drop pathLen invPath
        invVar    = Var (typeOf invExpr) letName

    ExprCL comp' <- pathR localPath (constT $ return $ inject invVar)
    debugMsg $ "loopInvariantHeadR " ++ pp (P.let_ letName invExpr comp')
    return $ inject $ P.let_ letName invExpr comp'
