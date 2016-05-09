{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}

-- | Float let-bindings as far top the top as possible to avoid evaluation of
-- computations in iterations that they do not depend on.
module Database.DSH.CL.Opt.LetFloating
  ( floatBindingsR
  ) where

import           Control.Arrow
import           Data.List

import           Database.DSH.CL.Kure
import           Database.DSH.CL.Lang
import           Database.DSH.CL.Opt.Auxiliary
import qualified Database.DSH.CL.Primitives     as P
import           Database.DSH.Common.Impossible
import           Database.DSH.Common.Lang

--------------------------------------------------------------------------------
-- Unary applications

floatAppE1R :: RewriteC Expr
floatAppE1R = do
    AppE1 ty p (Let _ x e1 e2) <- idR
    return $ Let ty x e1 (AppE1 ty p e2)

--------------------------------------------------------------------------------
-- Scalar unary applications

floatUnOpR :: RewriteC Expr
floatUnOpR = do
    UnOp ty p (Let _ x e1 e2) <- idR
    return $ Let ty x e1 (UnOp ty p e2)

--------------------------------------------------------------------------------
-- Binary applications

-- FIXME Rename to avoid name capturing
floatAppE2LeftR :: RewriteC Expr
floatAppE2LeftR = do
    AppE2 ty p (Let _ x e1 e2) re <- idR

    -- Do not rewrite if we would capture variables that occur free in the right
    -- expression.
    guardM $ x `notElem` freeVars re

    return $ Let ty x e1 (AppE2 ty p e2 re)

floatAppE2RightR :: RewriteC Expr
floatAppE2RightR = do
    AppE2 ty p le (Let _ x e1 e2) <- idR

    -- Do not rewrite if we would capture variables that occur free in the right
    -- expression.
    guardM $ x `notElem` freeVars le

    return $ Let ty x e1 (AppE2 ty p le e2)

--------------------------------------------------------------------------------
-- Scalar binary applications

-- FIXME Rename to avoid name capturing
floatBinOpLeftR :: RewriteC Expr
floatBinOpLeftR = do
    BinOp ty p (Let _ x e1 e2) re <- idR

    -- Do not rewrite if we would capture variables that occur free in the left
    -- expression.
    guardM $ x `notElem` freeVars re

    return $ Let ty x e1 (BinOp ty p e2 re)

floatBinOpRightR :: RewriteC Expr
floatBinOpRightR = do
    BinOp ty p le (Let _ x e1 e2) <- idR

    -- Do not rewrite if we would capture variables that occur free in the left
    -- expression.
    guardM $ x `notElem` freeVars le

    return $ Let ty x e1 (BinOp ty p le e2)

--------------------------------------------------------------------------------
-- Conditionals

floatIfCondR :: RewriteC Expr
floatIfCondR = do
    If ty (Let _ x e1 e2) t e <- idR

    -- Do not rewrite if we would capture variables that occur free in other
    -- sub-expressions.
    guardM $ x `notElem` (freeVars t ++ freeVars e)

    return $ Let ty x e1 (If ty e2 t e)

floatIfThenR :: RewriteC Expr
floatIfThenR = do
    If ty c (Let _ x e1 e2) e <- idR

    -- Do not rewrite if we would capture variables that occur free in other
    -- sub-expressions.
    guardM $ x `notElem` (freeVars c ++ freeVars e)

    return $ Let ty x e1 (If ty c e2 e)

floatIfElseR :: RewriteC Expr
floatIfElseR = do
    If ty c t (Let _ x e1 e2) <- idR

    -- Do not rewrite if we would capture variables that occur free in other
    -- sub-expressions.
    guardM $ x `notElem` (freeVars c ++ freeVars t)

    return $ Let ty x e1 (If ty c t e2)

--------------------------------------------------------------------------------
-- Tuple constructors

-- | Search for a floatable let-binding in a list of expressions.
letElem :: [Expr] -> [Ident] -> [Expr] -> Maybe (Ident, Expr, [Expr])
letElem (Let _ x e1 e2:es) fvs prevExprs
    | x `notElem` fvs =
      Just (x, e1, prevExprs ++ [e2] ++ es)
    | otherwise                                        =
      Nothing
letElem (e:es)              fvs prevExprs = letElem es fvs (prevExprs ++ [e])
letElem []                  _   _         = Nothing

floatTupleR :: RewriteC Expr
floatTupleR = do
    MkTuple ty es <- idR
    case letElem es (concatMap freeVars es)[] of
        Just (x, e1, es') -> return $ Let ty x e1 (MkTuple ty es')
        Nothing                -> fail "no let in tuple elements"

--------------------------------------------------------------------------------
-- Comprehensions

floatCompHeadR :: [Ident] -> RewriteC CL
floatCompHeadR blockingNames = do
    c@(Comp ty (Let _ x e1 e2) qs) <- promoteT idR
    guardM $ x `notElem` compBoundVars qs
    guardM $ x `notElem` freeVars c
    guardM $ null $ freeVars e1 `intersect` blockingNames
    return $ inject $ Let ty x e1 (Comp ty e2 qs)

letQualR :: [Ident] -> TransformC CL (Ident, Expr, Expr, PathC)
letQualR blockingNames = do
    Let _ x e1 e2 <- promoteT idR
    guardM $ x `notElem` blockingNames
    guardM $ null $ freeVars e1 `intersect` blockingNames
    path <- snocPathToPath <$> absPathT
    return (x, e1, e2, path)

letQualsR :: [Ident] -> TransformC CL (Ident, Expr, Expr, PathC)
letQualsR blockingNames = readerT $ \expr -> case expr of
    QualsCL (BindQ{} :* _)  -> pathT [QualsHead, BindQualExpr] (letQualR blockingNames)
                               <+ childT QualsTail (letQualsR blockingNames)
    QualsCL (GuardQ{} :* _) -> pathT [QualsHead, GuardQualExpr] (letQualR blockingNames)
                               <+ childT QualsTail (letQualsR blockingNames)
    QualsCL (S GuardQ{})    -> pathT [QualsSingleton, GuardQualExpr] (letQualR blockingNames)
    QualsCL (S BindQ{})     -> pathT [QualsSingleton, BindQualExpr] (letQualR blockingNames)
    _                       -> $impossible

floatCompQualR :: [Ident] -> RewriteC CL
floatCompQualR blockingNames = do
    (x, e1, e2, letPath) <- childT CompQuals (letQualsR blockingNames)
    localPath <- localizePathT letPath
    ExprCL comp' <- pathR localPath (constT $ return $ inject e2)
    return $ inject $ P.let_ x e1 comp'

floatCompR :: RewriteC CL
floatCompR = do
    c@(Comp _ _ qs) <- promoteT idR
    -- FIXME checking with *all* generator variables in the current
    -- comprehension is too conservative. It would be sufficient to consider
    -- those preceding the guard that is under investigation.
    let blockingNames = compBoundVars qs ++ freeVars c
    floatCompQualR blockingNames <+ floatCompHeadR blockingNames

--------------------------------------------------------------------------------

floatNonBindingR :: RewriteC Expr
floatNonBindingR = floatAppE1R
                   <+ floatUnOpR
                   <+ floatAppE2LeftR
                   <+ floatAppE2RightR
                   <+ floatBinOpLeftR
                   <+ floatBinOpRightR
                   <+ floatIfCondR
                   <+ floatIfThenR
                   <+ floatIfElseR
                   <+ floatTupleR

floatBindingR :: RewriteC CL
floatBindingR = floatCompR

floatBindingsR :: RewriteC CL
floatBindingsR = readerT $ \e -> case e of
    ExprCL{} -> (promoteT floatNonBindingR >>> injectT) <+ floatBindingR
    _        -> fail "only expressions"
