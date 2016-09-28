{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternSynonyms       #-}

module Database.DSH.FKL.Rewrite
    ( optimizeFKL
    , optimizeNormFKL
    ) where

import           Control.Arrow
import qualified Data.Foldable                as F
import           Data.List
import           Data.Monoid

import           Database.DSH.Common.Kure
import           Database.DSH.Common.Lang
import           Database.DSH.Common.Nat
import           Database.DSH.Common.Pretty

import           Database.DSH.Common.RewriteM
import           Database.DSH.Common.Type
import           Database.DSH.FKL.Kure
import           Database.DSH.FKL.Lang

import qualified Database.DSH.FKL.Primitives  as P

-- | Run a translate on an expression without context
applyExpr :: (Injection (ExprTempl l e) (FKL l e))
          => TransformF (FKL l e) b -> ExprTempl l e -> Either String b
applyExpr f e = fst <$> runRewriteM (applyT f initialCtx (inject e))

applyExprLog :: (Injection (ExprTempl l e) (FKL l e))
             => TransformF (FKL l e) b -> ExprTempl l e -> Either String (b, String)
applyExprLog f e =
    case runRewriteM (applyT f initialCtx (inject e)) of
        Left msg     -> Left msg
        Right (b, l) -> Right (b, F.foldl' (\s m -> s ++ "\n\n" ++ m) "" l)

--------------------------------------------------------------------------------
-- Computation of free and bound variables

freeVarsT :: Walker FlatCtx (FKL l e) => TransformF (FKL l e) [Ident]
freeVarsT = fmap nub
            $ crushbuT
            $ do (ctx, ExprFKL (Var _ v)) <- exposeT
                 guardM (v `freeIn` ctx)
                 return [v]

-- | Compute free variables of the given expression
freeVars :: (Walker FlatCtx (FKL l e), Injection (ExprTempl l e) (FKL l e))
         => ExprTempl l e -> [Ident]
freeVars = either error id . applyExpr freeVarsT


--------------------------------------------------------------------------------
-- Substitution

alphaLetR :: ( Injection (ExprTempl l e) (FKL l e)
             , Walker FlatCtx (FKL l e)
             , Typed e
             , Pretty l
             , Pretty e
             )
          => [Ident] -> RewriteF (FKL l e)
alphaLetR avoidNames = do
    ExprFKL (Let ty x e1 e2) <- idR
    x'                      <- freshNameT (x : freeVars e2 ++ avoidNames)
    let varTy = typeOf e1
    e2' <- childT LetBody (substR x (Var varTy x')) >>> projectT
    return $ inject $ Let ty x' e1 e2'

substR :: ( Injection (ExprTempl l e) (FKL l e)
          , Walker FlatCtx (FKL l e)
          , Typed e
          , Pretty l
          , Pretty e
          )
       => Ident -> ExprTempl l e -> RewriteF (FKL l e)
substR v s = readerT $ \expr -> case expr of
    -- Occurence of the variable to be replaced
    ExprFKL (Var _ n) | n == v     -> return $ inject s

    -- A let-binding that does not shadow 'v'.
    ExprFKL (Let _ x _ _) | x /= v ->
        if x `elem` freeVars s
        then alphaLetR (freeVars s) >>> substR v s
        else tryR $ anyR $ substR v s

    -- A let binding which shadows v -> don't descend into the body
    ExprFKL (Let _ x _ _) | v == x -> tryR $ childR LetBind (substR v s)

    -- For all other expressions, simply substitute in the children
    _                              -> tryR $ anyR $ substR v s

--------------------------------------------------------------------------------
-- Simple optimizations

-- | Count all occurences of an identifier for let-inlining.
countVarRefT :: Walker FlatCtx (FKL l e) => Ident -> TransformF (FKL l e) (Sum Int)
countVarRefT v = readerT $ \expr -> case expr of
    -- Occurence of the variable to be replaced
    ExprFKL (Var _ n) | n == v         -> return 1
                      | otherwise      -> return 0
    ExprFKL Table{}                    -> return 0
    ExprFKL Const{}                    -> return 0
    ExprFKL (Let _ n _ _) | n == v     -> childT LetBind (countVarRefT v)
                          | otherwise  -> allT (countVarRefT v)
    _                                  -> allT (countVarRefT v)


-- | Remove a let-binding that is not referenced.
unusedBindingR :: ( Injection (ExprTempl l e) (FKL l e)
                  , Walker FlatCtx (FKL l e)
                  , Pretty l
                  , Pretty e
                  )
               => RewriteF (FKL l e)
unusedBindingR = logR "fkl.unusedbinding" $ do
    ExprFKL (Let _ x _ e2) <- idR
    0                      <- childT LetBody $ countVarRefT x
    return $ inject e2


-- | Inline a let-binding that is only referenced once.
referencedOnceR :: ( Injection (ExprTempl l e) (FKL l e)
                   , Walker FlatCtx (FKL l e)
                   , Typed e
                   , Pretty e
                   , Pretty l
                   )
                => RewriteF (FKL l e)
referencedOnceR = logR "fkl.referencedonce" $ do
    ExprFKL (Let _ x e1 _) <- idR
    1            <- childT LetBody $ countVarRefT x
    childT LetBody $ substR x e1

simpleExpr :: ExprTempl l e -> Bool
simpleExpr Table{}                   = True
simpleExpr Var{}                     = True
simpleExpr (PApp1 _ (TupElem _) _ e) = simpleExpr e
simpleExpr _                         = False

-- | Inline a let-binding that binds a simple expression.
simpleBindingR :: ( Injection (ExprTempl l e) (FKL l e)
                  , Walker FlatCtx (FKL l e)
                  , Typed e
                  , Pretty e
                  , Pretty l
                  )
               => RewriteF (FKL l e)
simpleBindingR = logR "fkl.simplebinding" $ do
    ExprFKL (Let _ x e1 _) <- idR
    guardM $ simpleExpr e1
    childT LetBody $ substR x e1

--------------------------------------------------------------------------------
-- Rewrites that remove redundant combinations of shape operators
-- (forget and imprint)

pattern ImprintP :: Nat -> FExpr -> FExpr -> ExprTempl t ShapeExt
pattern ImprintP d e1 e2 <- Ext (Imprint d _ e1 e2)

pattern ForgetP :: Nat -> FExpr -> ExprTempl l ShapeExt
pattern ForgetP d e <- Ext (Forget d _ e)

-- | Remove nested occurences of 'imprint':
--
-- imprint_d (imprint_d e1 _) e2
-- =>
-- imprint_d e1 e2
--
-- The reasoning is simple: The inner 'imprint' attaches the outer 'd'
-- layers of 'e1' onto 'e2'. The outer 'imprint' takes exactly these
-- 'd' outer layers and attaches it to 'e2'. Therefore, we can use the
-- outer 'd' layers of 'e1' directly without the inner 'imprint'.
nestedimprintR :: RewriteF (FKL Lifted ShapeExt)
nestedimprintR = do
    ExprFKL (ImprintP d (ImprintP d' e1 _) e2) <- idR
    guardM $ d == d'
    return $ ExprFKL (P.imprint d' e1 e2)

-- | Remove combinations of forget and imprint that cancel each
-- other out.
forgetimprintR :: RewriteF (FKL Lifted ShapeExt)
forgetimprintR = do
    ExprFKL (ForgetP d (ImprintP d' _ xs)) <- idR
    guardM $ d == d'
    return $ ExprFKL xs

-- | If 'forget' removes /strictly more/ nesting than the nested 'imprint' adds,
-- we can remove the 'imprint' and 'forget' only the difference.
forgetimprintlargerR :: RewriteF (FKL Lifted ShapeExt)
forgetimprintlargerR = do
    ExtFKL (Forget d1 t (Ext (Imprint d2 _ _ xs))) <- idR
    guardM $ d1 > d2
    case d1 .- d2 of
        Just dd -> return $ ExtFKL (Forget dd t xs)
        Nothing -> fail "depths are not compatible"

-- | If 'forget' removes /strictly less/ nesting than the nested 'imprint'
-- adds, we can not remove one of the shape combinators. However, we
-- can decrease the depth of shape operations. 'imprint' adds the 'd2'
-- outer layers of 'e1' to 'e2'. Of those 'd2' outer layers, 'forget'
-- removes the outermost 'd1' (which are less than 'd2'). Effectively,
-- only the vectors 'd1' to 'd2' of 'e1' are added to
-- 'e2'. Consequentially, we can apply 'forget' first and only
-- 'imprint' the inner vectors.
--
-- forget_d1 (imprint_d2 e1 e2)
-- =>
-- imprint_(d_2 - d_1) (forget_d1 e1) e2
--
-- This rewrite does not immediately lead to a reduction of term
-- size. However, it decreases the depth of vectors that are
-- applied/forgotten. That might be a good thing on its own (but
-- propably irrelevant, because shape operations crucially do not have
-- runtime cost). Additionally, it can expose other rewrite
-- opportunities. This is very true e.g. in query 'expectedRevenueFor'
-- (dsh-tpch-other).
forgetimprintsmallerR :: RewriteF (FKL Lifted ShapeExt)
forgetimprintsmallerR = do
    ExprFKL (ForgetP d1 (ImprintP d2 e1 e2)) <- idR
    guardM $ d2 > d1
    case d2 .- d1 of
        Just dd -> return $ ExprFKL $ P.imprint dd (P.forget d1 e1) e2
        Nothing -> fail "depths are not compatible"

-- | 'forget'/'imprint' combinations are often obscured by
-- 'let'-bindings. This rewrite inlines a binding and succeeds if
-- other rewrites succeed in the resulting term.
boundforgetimprintR :: RewriteF (FKL Lifted ShapeExt)
boundforgetimprintR = do
    ExprFKL (Let _ x e1 _) <- idR
    childT LetBody (substR x e1 >>> anybuR rewrites)

  where
    rewrites =    forgetimprintR
               <+ nestedimprintR
               <+ forgetimprintlargerR
               <+ forgetimprintsmallerR

--------------------------------------------------------------------------------
-- Chained dist patterns

pattern DistP :: Type -> l -> ExprTempl l e -> ExprTempl l e -> ExprTempl l e
pattern DistP ty l e1 e2 = PApp2 ty Dist l e1 e2

-- | A binding that is referenced across more than one iteration level will lead
-- to a chain of dist operations due to nested environment lifting. This rewrite
-- deals with one particular instance of this pattern:
--
-- @
-- dist^1 (dist^0 x ys) zs
-- @
--
-- In this case, a value @x@ is first distributed over the outer iteration
-- context, resulting in a copy of @x@ for every element of @ys@. For each inner
-- list of @zs@, the corresponding copy of @x@ is then copied again to match
-- each element of said inner list. This multi-stage replication is not
-- necessary, though: We are dealing with exactly one value that is to be
-- replicated. We need a copy of that value @x@ for every element of an inner
-- list of @zs@, keeping the nesting structure of @zs@ intact. We can achieve
-- this in a more simple way by shortcutting the multi-stage replication:
--
-- @
-- imprint_1 zs (dist^0 x (forget_1 zs))
-- @
--
-- This rewrite is inspired by query 'cheaperSuppliersInRegionAvg2' when
-- approached with a top-down unnesting approach.
distChainR :: RewriteF (FKL Lifted ShapeExt)
distChainR = do
    ExprFKL (DistP _ Lifted (DistP _ NotLifted x _) zs) <- idR
    zsName <- freshNameT []
    let zsVar = Var (typeOf zs) zsName
    return $ inject $ P.let_ zsName zs
                             (P.imprint (Succ Zero) zsVar
                                                    (P.fdist x (P.forget (Succ Zero) zsVar)))

--------------------------------------------------------------------------------

fklOptimizations :: ( Injection (ExprTempl l e) (FKL l e)
                    , Walker FlatCtx (FKL l e)
                    , Typed e
                    , Pretty l
                    , Pretty e
                    )
                 => RewriteF (FKL l e)
fklOptimizations = anybuR $ unusedBindingR
                            <+ referencedOnceR
                            <+ simpleBindingR

fklNormOptimizations :: RewriteF (FKL Lifted ShapeExt)
fklNormOptimizations = repeatR $ anybuR rewrites
  where
    rewrites = unusedBindingR
               <+ referencedOnceR
               <+ simpleBindingR
               <+ forgetimprintR
               <+ forgetimprintlargerR
               <+ boundforgetimprintR
               <+ nestedimprintR
               <+ forgetimprintsmallerR
               <+ distChainR

optimizeNormFKL :: FExpr -> FExpr
optimizeNormFKL expr =
    case applyExpr (fklNormOptimizations >>> projectT) expr of
        Left _      -> expr
        Right expr' -> expr'

optimizeFKL :: LExpr -> LExpr
optimizeFKL expr =
    case applyExprLog (fklOptimizations >>> projectT) expr of
        Left _           -> expr
        Right (expr', _) -> expr'
