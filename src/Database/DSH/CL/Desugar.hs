{-# LANGUAGE PatternSynonyms       #-}

-- | Remove scalar literals from CL terms by binding them as singleton list
-- generators.
module Database.DSH.CL.Desugar
  ( bindScalarLiterals
  , wrapComprehension
  ) where

import           Control.Arrow

import           Database.DSH.Common.Lang

import           Database.DSH.CL.Kure
import qualified Database.DSH.CL.Primitives as P
import           Database.DSH.CL.Lang
import           Database.DSH.CL.Opt.Auxiliary

-- | Search for a scalar literal in an expression. Return the value and the path
-- to the literal.
searchScalarLiteralT :: TransformC CL (Either [Val] ScalarVal, Type , PathC)
searchScalarLiteralT = readerT $ \expr -> case expr of
    ExprCL (Lit ty (TupleV fs)) -> do
        path <- snocPathToPath <$> absPathT
        return (Left fs, ty, path)
    ExprCL (Lit ty (ScalarV v)) -> do
        path <- snocPathToPath <$> absPathT
        return (Right v, ty, path)
    ExprCL Comp{}              -> fail "don't traverse into comprehensions"
    _                          -> oneT searchScalarLiteralT

-- | Create a singleton list value from a scalar value.
wrapSingleton :: Either [Val] ScalarVal -> Val
wrapSingleton (Left fs) = ListV [TupleV fs]
wrapSingleton (Right v) = ListV [ScalarV v]

-- | Create a generator for a singleton literal list.
mkScalarLitGen :: Type -> Ident -> Either [Val] ScalarVal -> Qual
mkScalarLitGen scalarTy genName scalarVal =
    genName :<-: Lit (ListT scalarTy) (wrapSingleton scalarVal)

-- | Search for a scalar literal in the head of a comprehension and bind it as a
-- singleton qualifier.
bindScalarLiteralHeadR :: RewriteC CL
bindScalarLiteralHeadR = do
    ExprCL (Comp compTy h qs) <- idR
    (v, ty, path)         <- childT CompHead searchScalarLiteralT
    localPath             <- localizePathT path
    genName               <- pathT localPath (freshNameT [])
    let litVar = Var ty genName
    ExprCL h' <- constT (return $ inject h)
                 >>>
                 pathR (drop 1 localPath) (constT $ return $ inject litVar)
    let qs' = qs `appendNL` S (mkScalarLitGen ty genName v)
    return $ inject $ Comp compTy h' qs'

-- | Search for a scalar literal in the qualifiers of a comprehension and bind
-- it as a singleton qualifier.
bindScalarLiteralGensR :: RewriteC CL
bindScalarLiteralGensR = do
    ExprCL (Comp compTy h qs) <- idR
    (v, ty, path)         <- childT CompQuals searchScalarLiteralT
    localPath             <- localizePathT path
    genName               <- pathT localPath (freshNameT [])
    let litVar = Var ty genName
    QualsCL qs' <- constT (return $ inject qs)
                   >>>
                   pathR (drop 1 localPath) (constT $ return $ inject litVar)
    let qs'' = mkScalarLitGen ty genName v :* qs'
    return $ inject $ Comp compTy h qs''

-- | Search for scalar literals in a comprehension and bind them as singleton
-- generators.
bindScalarLiteralsR :: RewriteC CL
bindScalarLiteralsR = do
    ExprCL Comp{} <- idR
    repeatR bindScalarLiteralHeadR >+> repeatR bindScalarLiteralGensR

-- | Eliminate scalar literals from a CL expression by binding them as singleton
-- list generators in the enclosing comprehension.
bindScalarLiterals :: Expr -> Expr
bindScalarLiterals expr =
    case applyExpr (bindScalarLiteralsR >>> projectT) expr of
        Left _      -> expr
        Right expr' -> expr'

--------------------------------------------------------------------------------

-- | Ensure that the topmost construct in a CL expression is a comprehension.
--
-- This rewrite is valid because we allow only list-typed queries.
wrapComprehension :: Expr -> Expr
wrapComprehension e@Comp{} = e
wrapComprehension e        = P.concat sngIter
  where
    sngIter = Comp (ListT $ typeOf e) e (S $ "dswrap" :<-: (uncurry Lit sngUnitList))
