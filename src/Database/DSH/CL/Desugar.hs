{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}

-- | Remove scalar literals from CL terms by binding them as singleton list
-- generators.
module Database.DSH.CL.Desugar
  ( bindScalarLiterals
  , wrapComprehension
  , desugarBuiltins
  , eliminateScalarSingletons
  , mergeExtLiterals
  ) where

import           Control.Arrow

import           Database.DSH.Common.Impossible
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
-- Eliminate generators with singleton literal lists

pushSingletonGenQualsR :: RewriteC CL
pushSingletonGenQualsR = readerT $ \quals -> case quals of
    QualsCL ((y :<-: LitListP ty [ScalarV v]) :* (_ :<-: LitListP{}) :* _) -> do
        qs' <- childT QualsTail pushSingletonGenQualsR >>> projectT
        return $ inject $ (y :<-: LitListP ty [ScalarV v]) :* qs'
    QualsCL ((y :<-: LitListP ty [ScalarV v]) :* (x :<-: xs) :* qs) -> do
        guardM $ y `notElem` freeVars xs
        return $ inject $ (x :<-: xs) :* (y :<-: LitListP ty [ScalarV v]) :* qs
    QualsCL ((_ :<-: LitListP _ [ScalarV _]) :* S (_ :<-: LitListP{})) -> do
        fail "end of qualifier list, no match"
    QualsCL ((y :<-: LitListP ty [ScalarV v]) :* S (x :<-: xs)) -> do
        guardM $ y `notElem` freeVars xs
        return $ inject $ (x :<-: xs) :* S (y :<-: LitListP ty [ScalarV v])
    QualsCL (GuardQ p :* (y :<-: LitListP ty [ScalarV v]) :* qs) -> do
        guardM $ y `notElem` freeVars p
        return $ inject $ (y :<-: LitListP ty [ScalarV v]) :* GuardQ p :* qs
    QualsCL (GuardQ p :* S (y :<-: LitListP ty [ScalarV v]))     -> do
        guardM $ y `notElem` freeVars p
        return $ inject $ (y :<-: LitListP ty [ScalarV v]) :* S (GuardQ p)
    QualsCL (q :* _)                                             -> do
        qs' <- childT QualsTail pushSingletonGenQualsR >>> projectT
        return $ inject $ q :* qs'
    QualsCL (S _)                                                ->
        fail "end of qualifier list, no match"
    _                                                            ->
        $impossible

-- | Push scalar singleton list generators in front of guards as a preparation
-- for merging them into generator extensions.
pushSingletonGenR :: RewriteC CL
pushSingletonGenR = do
    Comp ty h _ <- promoteT idR
    qs' <- childT CompQuals pushSingletonGenQualsR >>> projectT
    return $ inject $ Comp ty h qs'

-- | Search for a generator with a literal singleton scalar list that can be
-- replaced with an extension of another generator. Returns the new qualifier
-- list, the tuplifying rewrite for the comprehension head and the tuplifying
-- rewrite for the qualifiers together with the position from which it needs to
-- be applied.
searchScalarSingletonR :: TransformC CL (NL Qual, RewriteC CL, Maybe (PathC, RewriteC CL))
searchScalarSingletonR = readerT $ \quals -> case quals of
    QualsCL ((x :<-: xs) :* (y :<-: LitListP _ [ScalarV v]) :* qs) -> do
        -- Sanity check
        guardM $ x /= y

        -- Tuplification in the qualifiers needs to be applied from here on.
        path <- snocPathToPath <$> absPathT

        -- A fresh name for the extension generator
        z    <- freshNameT $ [x,y] ++ compBoundVars qs

        let xt     = elemT $ typeOf xs
            yt     = typeOf v
            extGen = P.ext v xs
            tupR   = tuplifyR z (x, xt) (y, yt)

        -- Check the subsequent generators to see whether either x and/or y need
        -- to be replaced in the head (or not, because they are shadowed by
        -- subsequent generators).
        let headR = case fmap (fmap fst) $ sequence $ fmap fromGen qs of
                        Just ns
                            | x `elem` ns && y `elem` ns -> idR
                            | x `elem` ns                -> tuplifySecondR z xt (y, yt)
                            | y `elem` ns                -> tuplifyFirstR z (x, xt) yt
                            | otherwise                  -> tupR
                        Nothing                          -> tupR
        return ((z :<-: extGen) :* qs, headR, Just (path, tupR))

    QualsCL ((x :<-: xs) :* S (y :<-: LitListP _ [ScalarV v]))     -> do
        -- Sanity check
        guardM $ x /= y

        x'   <- freshNameT [x,y]
        let extGen = P.ext v xs
            tupR   = tuplifyR x' (x,elemT $ typeOf xs) (y,typeOf v)

        -- If there are no subsequent generators, we know that neither x or y
        -- are shadowed in the comprehension head. Furthermore, there is no need
        -- to return a tuplifying rewrite for subsequent generators (because
        -- there are none).
        return (S (x' :<-: extGen), tupR, Nothing)
    QualsCL (q :* _)                                               -> do
        (qs', headR, mQualsR) <- childT QualsTail searchScalarSingletonR
        return (q :* qs', headR, mQualsR)
    QualsCL (S _)                                                   -> do
        fail "bar"
    ExprCL _ -> $impossible
    QualCL _ -> $impossible

eliminateScalarSingletonR :: RewriteC CL
eliminateScalarSingletonR = do
    Comp{}                <- promoteT idR
    (qs', headR, mQualsR) <- childT CompQuals searchScalarSingletonR

    let uHeadR = extractT headR >>> projectT
        newQualsR = constT (pure $ QualsCL qs')
    uQualsR <- case mQualsR of
                   Just (qualsPath, qsR) -> do
                       localPath <- drop 1 <$> localizePathT qualsPath
                       pure $ extractT (pathR localPath qsR)
                   Nothing                  -> pure idR
    projectT >>> compR uHeadR (newQualsR >>> uQualsR >>> projectT) >>> injectT

eliminateScalarSingletonsR :: RewriteC CL
eliminateScalarSingletonsR = do
    Comp{} <- promoteT idR
    repeatR pushSingletonGenR >+> repeatR eliminateScalarSingletonR

-- | Replace singleton scalar literal list generators with generator extensions.
--
-- @
-- [ e | x <- xs, y <- [42], qs ]
-- =>
-- [ e[z.1/x][z.2/y] | z <- ext{42} xs, qs[z.1/x][z.2/y] ]
-- @
eliminateScalarSingletons :: Expr -> Expr
eliminateScalarSingletons e = tryRewrite (repeatR $ anytdR eliminateScalarSingletonsR) e

--------------------------------------------------------------------------------
-- Bind scalar literals in enclosing comprehensions

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
bindScalarLiterals = tryRewrite (anytdR bindScalarLiteralsR)

--------------------------------------------------------------------------------
-- Merge extensions into literal lists

mergeExtLiteralR :: RewriteC CL
mergeExtLiteralR = do
    AppE1 ty1 (Ext v) (Lit _ (ListV vs)) <- promoteT idR
    let vs' = map (\litVal -> TupleV [litVal, ScalarV v]) vs
    pure $ inject $ Lit ty1 (ListV vs')

-- | Merge scalar extensions into literal lists:
--
-- @ext{v} [v_1,...,v_n] => [<v_1,v>,...,<v_n,v>]@
--
-- This rewrite is important to prevent ext from floating to the top-level unit
-- comprehension wrapper and appear unlifted.
--
-- See TPC-H Q14 for an example.
mergeExtLiterals :: Expr -> Expr
mergeExtLiterals = tryRewrite (repeatR $ anytdR mergeExtLiteralR)

--------------------------------------------------------------------------------

-- | Ensure that the topmost construct in a CL expression is a comprehension.
--
-- This rewrite is valid because we allow only list-typed queries.
wrapComprehension :: Expr -> Expr
wrapComprehension e        = P.concat sngIter
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
