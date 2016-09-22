{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}

module Database.DSH.NKL.Rewrite
    ( substR
    , subst
    , freeVars
    , boundVars
    , optimizeNKL
    ) where

import           Control.Arrow
import           Data.List
import           Data.Monoid

import           Database.DSH.Common.Impossible

import           Database.DSH.Common.Lang
import           Database.DSH.Common.RewriteM
import           Database.DSH.Common.Type
import           Database.DSH.NKL.Kure
import           Database.DSH.NKL.Lang
import qualified Database.DSH.NKL.Primitives    as P

-- | Run a translate on an expression without context
applyExpr :: [Ident] -> TransformN Expr b -> Expr -> Either String b
applyExpr nameCtx f e = fst <$> runRewriteM (applyT f (initialCtx nameCtx) (inject e))

--------------------------------------------------------------------------------
-- Computation of free and bound variables

freeVarsT :: TransformN Expr [Ident]
freeVarsT = fmap nub $ crushbuT $ do (ctx, Var _ v) <- exposeT
                                     guardM (v `freeIn` ctx)
                                     return [v]

-- | Compute free variables of the given expression
freeVars :: Expr -> [Ident]
freeVars = either error id . applyExpr [] freeVarsT

boundVarsT :: TransformN Expr [Ident]
boundVarsT = fmap nub $ crushbuT $ readerT $ \expr -> case expr of
     Iterator _ _ v _ -> return [v]
     Let _ v _ _      -> return [v]
     _                -> return []

-- | Compute all names that are bound in the given expression. Note
-- that the only binding forms in NKL are comprehensions or 'let'
-- bindings.
boundVars :: Expr -> [Ident]
boundVars = either error id . applyExpr [] boundVarsT

--------------------------------------------------------------------------------
-- Substitution

subst :: [Ident] -> [(Ident, Expr)] -> Expr -> Expr
subst nameCtx substDict e = either (const e) id $ applyExpr nameCtx (substR substDict) e

alphaCompR :: [Ident] -> RewriteN Expr
alphaCompR avoidNames = do
    Iterator compTy h x _  <- idR
    x'                     <- freshNameT (x : freeVars h ++ avoidNames)
    let varTy = elemT compTy
    iteratorT (tryR $ substR [(x, Var varTy x')])
              idR
              (\_ h' _ xs' -> Iterator compTy h' x' xs')

alphaLetR :: [Ident] -> RewriteN Expr
alphaLetR avoidNames = do
    Let letTy x e1 e2 <- idR
    x'                <- freshNameT (x : freeVars e2 ++ avoidNames)
    let varTy = typeOf e1
    letT idR (tryR $ substR [(x, Var varTy x')]) (\_ _ e1' e2' -> Let letTy x' e1' e2')

-- | Replace /all/ references to variables in a dictionary with the
-- corresponding expression.
substR :: [(Ident, Expr)] -> RewriteN Expr
substR []        = idR
substR substDict = readerT $ \expr -> case expr of
    Var _ n ->
        case lookup n substDict of
            -- Occurence of a variable to be replaced
            Just s  -> return s
            -- Some other variable
            Nothing -> idR

    -- Keep only those bindings from the substitution dictionary which are not
    -- shadowed by the generator variable. If the generator variable occurs free
    -- in one of the substitutes, we rename the iterator to avoid name
    -- capturing.
    Iterator _ h x _ | not (null $ freeVars h `intersect` map fst substDict) ->
        let notShadowed = filter ((/= x) . fst) substDict
            substFreeVars = concatMap (freeVars . snd) notShadowed
        in if x `elem` substFreeVars
           then     childR IteratorSource (substR substDict)
                >>> alphaCompR substFreeVars
                >>> childR IteratorHead (substR notShadowed)
           else iteratorR (substR notShadowed) (substR substDict)

    -- Keep only those bindings from the substitution dictionary which are not
    -- shadowed by the let-bound variable. If the let-bound variable occurs free
    -- in one of the substitutes, we rename the let-binding to avoid name
    -- capturing.
    Let _ x _ e2 | not (null $ freeVars e2 `intersect` map fst substDict) ->
        let notShadowed = filter ((/= x) . fst) substDict
            substFreeVars = concatMap (freeVars . snd) notShadowed
        in if x `elem` substFreeVars
           then     childR LetBind (substR substDict)
                >>> alphaLetR substFreeVars
                >>> childR LetBody (substR notShadowed)
           else letR (substR substDict) (substR notShadowed)

    _                                         -> anyR $ substR substDict

--------------------------------------------------------------------------------
-- Simple optimizations

-- | This function inlines let-bound expressions. In contrast to
-- general substitution, we do not inline into comprehensions, even if
-- we could. The reason is that expressions should not be evaluated
-- iteratively if they are loop-invariant.
inlineBindingR :: Ident -> Expr -> RewriteN Expr
inlineBindingR v s = readerT $ \expr -> case expr of
    -- Occurence of the variable to be replaced
    Var _ n | n == v          -> return $ inject s

    -- If a let-binding shadows the name we substitute, only descend
    -- into the bound expression.
    Let _ n _ _ | n == v      -> promoteR $ letR idR (extractR $ inlineBindingR v s)
                | otherwise   ->
        if n `elem` freeVars s
        -- If the let-bound name occurs free in the substitute,
        -- alpha-convert the binding to avoid capturing the name.
        then $unimplemented >>> anyR (inlineBindingR v s)
        else anyR $ inlineBindingR v s

    -- We don't inline into comprehensions to avoid conflicts with
    -- loop-invariant extraction.
    Iterator{}                -> idR
    _                         -> anyR $ inlineBindingR v s

pattern ConcatP :: Type -> Expr -> Expr
pattern ConcatP t xs <- AppE1 t Concat xs

pattern SingletonP :: Expr -> Expr
pattern SingletonP e <- AppE1 _ Singleton e

pattern RestrictP :: Expr -> Expr
pattern RestrictP e  <- AppE1 _ Restrict e

-- concatMap (\x -> [e x]) xs
-- concat [ [ e x ] | x <- xs ]
-- =>
-- [ e x | x <- xs ]
singletonHeadR :: RewriteN Expr
singletonHeadR = do
    -- Do not apply at the expression top-level: We must not eliminate the
    -- topmost iterator to guarantee that all expressions are compiled
    -- iteratively.
    []                                         <- snocPathToPath <$> absPathT
    ConcatP t (Iterator _ (SingletonP e) x xs) <- idR
    return $ Iterator t e x xs

-- | Count all occurences of an identifier for let-inlining.
countVarRefT :: Ident -> TransformN Expr (Sum Int)
countVarRefT v = readerT $ \expr -> case expr of
    -- Occurence of the variable to be replaced
    Var _ n | n == v         -> return 1
            | otherwise      -> return 0

    Let _ n _ _ | n == v     -> letT (constT $ return 0)
                                     (countVarRefT v)
                                     (\_ _ c1 c2 -> c1 + c2)
                | otherwise  -> letT (countVarRefT v)
                                     (countVarRefT v)
                                     (\_ _ c1 c2 -> c1 + c2)

    Iterator _ _ x _ | v == x -> iteratorT (constT $ return 0)
                                           (countVarRefT v)
                                           (\_ c1 _ c2 -> c1 + c2)
                     | otherwise -> iteratorT (countVarRefT v)
                                              (countVarRefT v)
                                              (\_ c1 _ c2 -> c1 + c2)

    Table{}                  -> return 0
    Const{}                  -> return 0
    _                        -> allT (countVarRefT v)

-- | Remove a let-binding that is not referenced.
unusedBindingR :: RewriteN Expr
unusedBindingR = do
    Let _ x _ e2 <- idR
    0            <- childT LetBody $ countVarRefT x
    return e2

-- | Inline a let-binding that is only referenced once.
referencedOnceR :: RewriteN Expr
referencedOnceR = do
    Let _ x e1 _ <- idR
    1            <- childT LetBody $ countVarRefT x

    -- We do not inline into comprehensions, but 'countVarRef' counts
    -- all occurences including those in comprehensions. For this
    -- reason, we check if the occurence was actually eliminated by
    -- inlining and fail otherwise.
    body' <- childT LetBody (inlineBindingR x e1)
    0     <- constT (return body') >>> countVarRefT x
    return body'

simpleExpr :: Expr -> Bool
simpleExpr Table{} = True
simpleExpr Var{}   = True
simpleExpr _       = False

-- | Inline a let-binding that binds a simple expression.
simpleBindingR :: RewriteN Expr
simpleBindingR = do
    Let _ x e1 _ <- idR
    guardM $ simpleExpr e1
    childT LetBody $ substR [(x, e1)]

-- | Eliminate an iterator that does not perform any work.
identityIteratorR :: RewriteN Expr
identityIteratorR = do
    Iterator _ (Var _ x) x' xs <- idR
    guardM $ x == x'
    return xs

-- | Push an iterator expression into a Sort operator to get a more
-- compact NKL expression. Note: Effectively, this rewrite pulls up
-- sorting in the plan. For sorting, this is propably OK. For
-- Restrict, though, that would not be a good idea.
--
-- [ f x | x <- sort [ (g y, h y) | y <- ys ] ]
-- =>
-- sort [ (f [g y/x], h y) | y <- ys ]
mergeSortIteratorR :: RewriteN Expr
mergeSortIteratorR = do
    Iterator _ f x (AppE1 _ Sort (Iterator _ (MkTuple _ [g, h]) y ys)) <- idR
    g' <- constT (return f) >>> substR [(x, g)]
    let ft = typeOf f
        pt = TupleT [ft, PBoolT]
    return $ AppE1 (ListT ft) Sort (Iterator (ListT pt) (MkTuple pt [g', h]) y ys)

-- | Merge two adjacent restricts into one.
--
-- restrict [ (x, p1 x) | x <- restrict [ (y, p2 y) | y <- ys ] ]
-- =>
-- restrict [ (y, p1[y/x] y && p2 y) | y <- ys ]
mergeRestrictR :: RewriteN Expr
mergeRestrictR = do
    RestrictP (Iterator _ (MkTuple _ [Var _ x', p1])
                          x
                          (RestrictP (Iterator _ (MkTuple _ [Var _ y', p2])
                                     y
                                     ys)))                                  <- idR
    guardM $ x == x'
    guardM $ y == y'
    let yt  = elemT $ typeOf ys
        yst = ListT yt
    p1' <- constT (return p1) >>> substR [(x, Var yt y)]
    let p = BinOp PBoolT (SBBoolOp Conj) p1' p2
    return $ P.restrict (Iterator yst (P.tuple [Var yt y, p]) y ys)

nklOptimizations :: RewriteN Expr
nklOptimizations = anybuR $ singletonHeadR
                            <+ unusedBindingR
                            <+ referencedOnceR
                            <+ simpleBindingR
                            <+ identityIteratorR
                            <+ mergeSortIteratorR
                            <+ mergeRestrictR

optimizeNKL :: Expr -> Expr
optimizeNKL expr =
    case applyExpr [] nklOptimizations expr of
        Left _      -> expr
        Right expr' -> expr'

