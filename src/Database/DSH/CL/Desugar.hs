{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}

-- | Remove scalar literals from CL terms by binding them as singleton list
-- generators.
module Database.DSH.CL.Desugar
  ( bindComplexLiterals
  , wrapComprehension
  , desugarBuiltins
  ) where

import           Control.Arrow

import           Database.DSH.Common.Lang

import           Database.DSH.CL.Kure
import           Database.DSH.CL.Lang
import           Database.DSH.CL.Opt.Auxiliary
import qualified Database.DSH.CL.Primitives     as P

--------------------------------------------------------------------------------

-- | Try a rewrite once on an expression. If it fails, return the original
-- expression.
tryRewrite :: RewriteC CL -> Expr -> Expr
tryRewrite r expr =
    case applyExpr (r >>> projectT) expr of
        Left _      -> expr
        Right expr' -> expr'

--------------------------------------------------------------------------------
-- Bind scalar literals in enclosing comprehensions

isScalar :: Val -> Bool
isScalar (ListV _)   = False
isScalar (TupleV vs) = all isScalar vs
isScalar (ScalarV _) = True

-- | Search for a scalar literal in an expression. Return the value and the path
-- to the literal.
searchComplexLiteralT :: TransformC CL (Either [Val] ScalarVal, Type , PathC)
searchComplexLiteralT = readerT $ \expr -> case expr of
    ExprCL (Lit ty (TupleV fs)) -> do
        guardM $ not $ all isScalar fs
        path <- snocPathToPath <$> absPathT
        return (Left fs, ty, path)
    ExprCL Comp{}              -> fail "don't traverse into comprehensions"
    _                          -> oneT searchComplexLiteralT

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
bindComplexLiteralHeadR :: RewriteC CL
bindComplexLiteralHeadR = do
    ExprCL (Comp compTy h qs) <- idR
    (v, ty, path)         <- childT CompHead searchComplexLiteralT
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
bindComplexLiteralGensR :: RewriteC CL
bindComplexLiteralGensR = do
    ExprCL (Comp compTy h qs) <- idR
    (v, ty, path)         <- childT CompQuals searchComplexLiteralT
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
bindComplexLiteralsR :: RewriteC CL
bindComplexLiteralsR = do
    ExprCL Comp{} <- idR
    repeatR bindComplexLiteralHeadR >+> repeatR bindComplexLiteralGensR

-- | Eliminate scalar literals from a CL expression by binding them as singleton
-- list generators in the enclosing comprehension.
bindComplexLiterals :: Expr -> Expr
bindComplexLiterals = tryRewrite (anytdR bindComplexLiteralsR)

--------------------------------------------------------------------------------

-- | Ensure that the topmost construct in a CL expression is a comprehension.
--
-- This rewrite is valid because we allow only list-typed queries.
wrapComprehension :: Expr -> Expr
wrapComprehension e        =
    case e of
        Comp _ _ (S (BindQ _ genExp)) ->
            case genExp of
                Lit{}   -> e
                Table{} -> e
                _       -> P.concat sngIter
        _ -> P.concat sngIter
  where
    sngIter = Comp (ListT $ typeOf e) e (S $ "dswrap" :<-: (uncurry Lit sngUnitList))

--------------------------------------------------------------------------------

desugarNullR :: RewriteC CL
desugarNullR = do
    ExprCL (AppE1 _ Null e) <- idR
    return $ inject $ P.eq (P.length e) (Lit PIntT (ScalarV $ IntV 0))

desugarBuiltinsR :: RewriteC CL
desugarBuiltinsR = anytdR desugarNullR

-- | Remove builtins that are not available in NKL.
desugarBuiltins :: Expr -> Expr
desugarBuiltins = tryRewrite desugarBuiltinsR
