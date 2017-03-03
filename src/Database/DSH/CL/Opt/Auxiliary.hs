{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf            #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TupleSections         #-}

-- | Common tools for rewrites
module Database.DSH.CL.Opt.Auxiliary
    ( applyExpr
    , applyExprLog
    , applyInjectable
      -- * Monad rewrites with additional state
    , TuplifyM
      -- * Convert join predicates into general expressions
    , fromScalarExpr
      -- * Converting predicate expressions into join predicates
    , toScalarExpr
    , toScalarExprT
    , splitJoinPredM
    , splitJoinPredE
    -- , joinConjunctsT
    , conjuncts
      -- * Helpers on scalar expressions
    , firstOnly
    , untuplifyScalarExpr
    , flipRelOp
      -- * Pushing guards towards the front of a qualifier list
    , isThetaJoinPred
    , isSemiJoinPred
    , isAntiJoinPred
    , isFlatExpr
      -- * Free and bound variables
    , freeVars
    , freeVarsS
    , boundVars
    , compBoundVars
      -- * Substituion
    , substM
    , substNoCompM
    , substR
    , substE
    , substCompE
    , substCompContE
    , tuplifyR
    , tuplifyE
    , tuplifyCompE
    , tuplifyCompContE
    , tuplifyFirstR
    , tuplifySecondR
    , unTuplifyR
    , unTuplifyPathR
      -- * Combining generators and guards
    , insertGuard
      -- * Generic iterator to merge guards into generators
    , Comp(..)
    , MergeGuard
    , mergeGuardsIterR
      -- * Classification of expressions
    , complexPrim1
    , complexPrim2
    , fromGuard
    , fromQual
    , fromGen
    , isFilteringJoin
      -- * NL spine traversal
    , onetdSpineT
    , onetdSpineR
      -- * Path utilities
    , localizePathT
      -- * Fold/Group Fusion
    , searchAggregatedGroupT
    , traverseGuardsT
      -- * Pattern synonyms for expressions
    , pattern ConcatP
    , pattern SingletonP
    , pattern GuardP
    , pattern SemiJoinP
    , pattern NestJoinP
    , pattern GroupJoinP
    , pattern GroupAggP
    , pattern AndP
    , pattern OrP
    , pattern SortP
    , pattern GroupP
    , pattern NotP
    , pattern EqP
    , pattern LengthP
    , pattern NullP
    , pattern FalseP
    , pattern TrueP
    , pattern TupFirstP
    , pattern TupSecondP
    , pattern (:<-:)
    , pattern LitListP
    , pattern SingleJoinPredP
    ) where

import           Control.Arrow
import           Control.Monad
import           Control.Monad.Reader
import           Data.Either
import qualified Data.Foldable                  as F
import           Data.List
import           Data.List.NonEmpty             (NonEmpty ((:|)))
import           Data.Semigroup                 hiding (First)
import qualified Data.Set                       as S
import           Text.Printf

import           Language.KURE

import           Database.DSH.CL.Kure
import           Database.DSH.CL.Lang
import           Database.DSH.Common.Impossible
import           Database.DSH.Common.Kure
import           Database.DSH.Common.Lang
import           Database.DSH.Common.Nat
import           Database.DSH.Common.Pretty
import           Database.DSH.Common.RewriteM

-- | A version of the CompM monad in which the state contains an additional
-- rewrite. Use case: Returning a tuplify rewrite from a traversal over the
-- qualifier list so that it can be applied to the head expression.
type TuplifyM = RewriteStateM (RewriteC CL) RewriteLog

-- | Run a translate on an expression without context
applyExpr :: TransformC CL b -> Expr -> Either String b
applyExpr f e = fst <$> runRewriteM (applyT f initialCtx (inject e))

-- | Run a translate on an expression without context and return the log.
applyExprLog :: TransformC CL b -> Expr -> Either String (b, String)
applyExprLog f e =
    case runRewriteM (applyT f initialCtx (inject e)) of
        Left msg     -> Left msg
        Right (b, l) -> Right (b, F.foldl' (\s m -> s ++ "\n\n" ++ m) "" l)

-- | Run a translate on any value which can be injected into CL
applyInjectable :: Injection a CL => TransformC CL b -> a -> Either String b
applyInjectable t e = fst <$> runRewriteM (applyT t initialCtx (inject e))

--------------------------------------------------------------------------------
-- Rewrite join predicates into general expressions.

-- | 'fromScalarExpr n e' rewrites scalar expression 'e' into a general
-- expression and uses the name 'n' for the input variable.
fromScalarExpr :: Ident -> ScalarExpr -> Expr
fromScalarExpr n e@(JBinOp op e1 e2)    = BinOp (typeOf e) op (fromScalarExpr n e1) (fromScalarExpr n e2)
fromScalarExpr n e@(JUnOp op e1)        = UnOp (typeOf e) op (fromScalarExpr n e1)
fromScalarExpr n e@(JTupElem tupIdx e1) = AppE1 (typeOf e) (TupElem tupIdx) (fromScalarExpr n e1)
fromScalarExpr _ (JLit ty val)          = Lit ty val
fromScalarExpr n (JInput ty)            = Var ty n

--------------------------------------------------------------------------------
-- Rewrite general expressions into equi-join predicates

toScalarExpr :: Ident -> Expr -> Maybe ScalarExpr
toScalarExpr n (AppE1 _ (TupElem i) e) = JTupElem i <$> toScalarExpr n e
toScalarExpr n (BinOp _ o e1 e2)       = JBinOp o <$> toScalarExpr n e1
                                                   <*> toScalarExpr n e2
toScalarExpr n (UnOp _ o e)            = JUnOp o <$> toScalarExpr n e
toScalarExpr _ (Lit t v)               = pure $ JLit t v
toScalarExpr n (Var t x)
    | n == x    = pure $ JInput t
    | otherwise = mzero
toScalarExpr _ _                       = mzero

toScalarExprT :: Ident -> TransformC Expr ScalarExpr
toScalarExprT n = do
    e <- idR
    case toScalarExpr n e of
        Nothing -> fail "not a scalar expression"
        Just s  -> pure s

flipRelOp :: BinRelOp -> BinRelOp
flipRelOp Eq  = Eq
flipRelOp NEq = NEq
flipRelOp Gt  = Lt
flipRelOp Lt  = Gt
flipRelOp GtE = LtE
flipRelOp LtE = GtE

-- | Try to transform an expression into a thetajoin predicate. This
-- will fail if either the expression does not have the correct shape
-- (relational operator with simple projection expressions on both
-- sides) or if one side of the predicate has free variables which are
-- not the variables of the qualifiers given to the function.
splitJoinPred :: Ident -> Ident -> Expr -> Maybe (JoinConjunct ScalarExpr)
splitJoinPred x y e =
    case e of
        BinOp _ (SBRelOp op) e1 e2 -> do
            [x'] <- pure $ freeVars e1
            [y'] <- pure $ freeVars e2
            if | x == x' && y == y' -> JoinConjunct <$> toScalarExpr x e1
                                                    <*> pure op
                                                    <*> toScalarExpr y e2
               | y == x' && x == y' -> JoinConjunct <$> toScalarExpr x e2
                                                    <*> pure (flipRelOp op)
                                                    <*> toScalarExpr y e1
               | otherwise          -> mzero
        _ -> mzero

splitJoinPredM :: MonadCatch m => Ident -> Ident -> Expr -> m (JoinConjunct ScalarExpr)
splitJoinPredM x y e =
    case splitJoinPred x y e of
        Just s  -> pure s
        Nothing -> fail "not a join predicate"

splitJoinPredE :: Ident -> Ident -> Expr -> Either Expr (JoinConjunct ScalarExpr)
splitJoinPredE x y e =
    case splitJoinPred x y e of
        Just s  -> Right s
        Nothing -> Left e

-- | Split a combination of logical conjunctions into its sub-terms.
conjuncts :: Expr -> NonEmpty Expr
conjuncts (BinOp _ (SBBoolOp Conj) e1 e2) = conjuncts e1 <> conjuncts e2
conjuncts e                               = pure e

--------------------------------------------------------------------------------
-- Helpers on scalar expressions

-- | Check whether a scalar expression refers only to the first tuple component
-- of the input.
firstOnly :: ScalarExpr -> Bool
firstOnly (JBinOp _ e1 e2)          = firstOnly e1 && firstOnly e2
firstOnly (JUnOp _ e)               = firstOnly e
firstOnly (JTupElem First JInput{}) = True
firstOnly (JTupElem _     JInput{}) = False
firstOnly (JTupElem _     e)        = firstOnly e
firstOnly JLit{}                    = True
firstOnly JInput{}                  = $impossible

-- | Change a scalar expression that only refers to the first tuple component of
-- the input to refer directly to the input.
untuplifyScalarExpr :: ScalarExpr -> ScalarExpr
untuplifyScalarExpr (JBinOp op e1 e2)                          = JBinOp op (untuplifyScalarExpr e1) (untuplifyScalarExpr e2)
untuplifyScalarExpr (JUnOp op e)                               = JUnOp op (untuplifyScalarExpr e)
untuplifyScalarExpr (JTupElem First (JInput (TupleT [t1, _]))) = JInput t1
untuplifyScalarExpr (JTupElem _ (JInput _))                    = $impossible
untuplifyScalarExpr (JTupElem idx e)                           = JTupElem idx (untuplifyScalarExpr e)
untuplifyScalarExpr (JLit ty val)                              = JLit ty val
untuplifyScalarExpr (JInput _)                                 = $impossible

--------------------------------------------------------------------------------
-- Distinguish certain kinds of guards

-- | An expression qualifies for a thetajoin predicate if both sides
-- are scalar expressions on exactly one of the join candidate
-- variables.
isThetaJoinPred :: Ident -> Ident -> Expr -> Bool
isThetaJoinPred x y (BinOp _ (SBRelOp _) e1 e2) =
    isFlatExpr e1 && isFlatExpr e1
    && ([x] == freeVars e1 && [y] == freeVars e2
        || [x] == freeVars e2 && [y] == freeVars e1)
isThetaJoinPred _ _ _ = False

-- | Does the predicate look like an existential quantifier?
isSemiJoinPred :: Ident -> Expr -> Bool
isSemiJoinPred x (OrP (Comp _ p (S (BindQ y _)))) = isThetaJoinPred x y p
isSemiJoinPred _  _                               = False

-- | Does the predicate look like an universal quantifier?
isAntiJoinPred :: Ident -> Expr -> Bool
isAntiJoinPred x (AndP (Comp _ p (S (BindQ y _)))) = isThetaJoinPred x y p
isAntiJoinPred _  _                                = False

isFlatExpr :: Expr -> Bool
isFlatExpr expr =
    case expr of
        AppE1 _ (TupElem _) e -> isFlatExpr e
        UnOp _ _ e            -> isFlatExpr e
        BinOp _ _ e1 e2       -> isFlatExpr e1 && isFlatExpr e2
        Var _ _               -> True
        Lit _ _               -> True
        _                     -> False

--------------------------------------------------------------------------------
-- Computation of free variables

-- | Compute free variables of the given expression
freeVarsS :: Expr -> S.Set Ident
freeVarsS Table{}           = S.empty
freeVarsS (AppE1 _ _ e)     = freeVarsS e
freeVarsS (AppE2 _ _ e1 e2) = freeVarsS e1 `S.union` freeVarsS e2
freeVarsS (BinOp _ _ e1 e2) = freeVarsS e1 `S.union` freeVarsS e2
freeVarsS (UnOp _ _ e)      = freeVarsS e
freeVarsS (If _ e1 e2 e3)   = freeVarsS e1 `S.union` freeVarsS e2 `S.union` freeVarsS e3
freeVarsS Lit{}             = S.empty
freeVarsS (Var _ n)         = S.singleton n
freeVarsS (Comp _ h qs)     = genFree `S.union` (freeVarsS h `S.difference` genBound)
  where
    (genBound, genFree) = foldl' go (S.empty, S.empty) qs

    go (gb, gf) (BindQ x e) = (S.insert x gb, gf `S.union` (freeVarsS e `S.difference` gb))
    go (gb, gf) (GuardQ p)  = (gb, gf `S.union` (freeVarsS p `S.difference` gb))
freeVarsS (MkTuple _ es)    = S.unions (map freeVarsS es)
freeVarsS (Let _ x e1 e2)   = freeVarsS e1 `S.union` (S.delete x (freeVarsS e2))

-- | Compute free variables of the given expression
freeVars :: Expr -> [Ident]
freeVars = S.toList . freeVarsS

-- | Compute all identifiers bound by a qualifier list
compBoundVars :: F.Foldable f => f Qual -> [Ident]
compBoundVars = F.foldr aux []
  where
    aux :: Qual -> [Ident] -> [Ident]
    aux (BindQ n _) ns = n : ns
    aux (GuardQ _) ns  = ns

boundVarsS :: Expr -> S.Set Ident
boundVarsS Table{}           = S.empty
boundVarsS (AppE1 _ _ e)     = boundVarsS e
boundVarsS (AppE2 _ _ e1 e2) = boundVarsS e1 `S.union` boundVarsS e2
boundVarsS (BinOp _ _ e1 e2) = boundVarsS e1 `S.union` boundVarsS e2
boundVarsS (UnOp _ _ e)      = boundVarsS e
boundVarsS (If _ e1 e2 e3)   = boundVarsS e1 `S.union` boundVarsS e2 `S.union` boundVarsS e3
boundVarsS Lit{}             = S.empty
boundVarsS (Var _ n)         = S.singleton n
boundVarsS (Comp _ h qs)     = boundVarsQualsS qs `S.union` boundVarsS h
boundVarsS (MkTuple _ es)    = S.unions (map boundVarsS es)
boundVarsS (Let _ x e1 e2)   = S.insert x $ boundVarsS e1 `S.union` boundVarsS e2

boundVarsQualsS :: NL Qual -> S.Set Ident
boundVarsQualsS qs = foldl' go S.empty qs
  where
    go gb (BindQ x e) = S.insert x $ boundVarsS e `S.union` gb
    go gb (GuardQ p)  = boundVarsS p `S.union` gb

-- | Compute all names that are bound in the given expression. Note that the
-- only binding forms in CL are comprehensions and 'let' bindings.
boundVars :: Expr -> [Ident]
boundVars = S.toList . boundVarsS

--------------------------------------------------------------------------------
-- Substitution

-- | 'substR v se' is a rewrite that /exhaustively/ substitutes term 'se' for a
-- variable 'v'.
substR :: Ident -> Expr -> RewriteC CL
substR v se = readerT $ \cl -> case cl of
    ExprCL e -> do
        scope <- S.fromList <$> inScopeNames <$> contextT
        let s = Subst { inScope   = scope
                      , substVar  = v
                      , substExpr = se
                      , substFvs  = freeVarsS se
                      , compCont  = substComp
                      }
        pure $ inject $ runReader (subst e) s
    n       -> error $ printf "substR: non-expr node %s on subst %s -> %s" (pp n) v (pp se)

-- | 'substM v se e' /exhaustively/ substitutes term 'se' for a variable 'v' in
-- term 'e'.
substM :: Ident -> Expr -> Expr -> TransformC a Expr
substM v se e = contextonlyT $ \c -> do
    let s = Subst { inScope   = S.fromList $ inScopeNames c
                  , substVar  = v
                  , substExpr = se
                  , substFvs  = freeVarsS se
                  , compCont  = substComp
                  }
    pure $ inject $ runReader (subst e) s

-- | 'substNoCompM v se e' substitutes term 'se' for variable 'v' in 'e' but
-- does not traverse into comprehensions. The resulting term may have free
-- occurences of 'v'.
substNoCompM :: Ident -> Expr -> Expr -> TransformC a Expr
substNoCompM v se e = contextonlyT $ \c -> do
    let s = Subst { inScope   = S.fromList $ inScopeNames c
                  , substVar  = v
                  , substExpr = se
                  , substFvs  = freeVarsS se
                  , compCont  = noSubstComp
                  }
    pure $ inject $ runReader (subst e) s

substE :: S.Set Ident -> Ident -> Expr -> Expr -> Expr
substE scopeNames v se e =
    let s = Subst { inScope   = scopeNames
                  , substVar  = v
                  , substExpr = se
                  , substFvs  = freeVarsS se
                  , compCont  = substComp
                  }
    in runReader (subst e) s

substCompContE :: S.Set Ident -> Ident -> Expr -> NL Qual -> (NL Qual, Expr -> Expr)
substCompContE scopeNames v se qs =
    let s = Subst { inScope   = scopeNames
                  , substVar  = v
                  , substExpr = se
                  , substFvs  = freeVarsS se
                  , compCont  = substComp
                  }
    in runReader (substComp qs) s

substCompE :: S.Set Ident -> Ident -> Expr -> NL Qual -> Expr -> (NL Qual, Expr)
substCompE scopeNames v se qs h =
    let s = Subst { inScope   = scopeNames
                  , substVar  = v
                  , substExpr = se
                  , substFvs  = freeVarsS se
                  , compCont  = substComp
                  }
        (qs', headCont) = runReader (substComp qs) s
    in (qs', headCont h)


data Subst = Subst
    { inScope   :: S.Set Ident
    , substVar  :: Ident
    , substExpr :: Expr
    , substFvs  :: S.Set Ident
    , compCont  :: NL Qual -> Reader Subst (NL Qual, Expr -> Expr)
    }

bindName :: Ident -> Subst -> Subst
bindName x s = s { inScope = S.insert x (inScope s) }

substFreshName :: S.Set Ident -> Ident
substFreshName avoidNames = go (0 :: Int)
  where
    go i = let v = "s" ++ show i
           in if v `S.member` avoidNames
              then go (i + 1)
              else v

alphaLet :: S.Set Ident -> Ident -> Expr -> Expr -> Reader Subst (Ident, Expr)
alphaLet avoidNames x e1 e2 = do
    let z = substFreshName avoidNames
    s <- ask
    let s' = s { inScope   = S.insert z $ S.delete x $ inScope s
               , substVar  = x
               , substExpr = Var (typeOf e1) z
               , substFvs  = S.singleton z
               }
    e2' <- local (const s') (subst e2)
    pure (z, e2')

alphaComp :: S.Set Ident -> Ident -> Expr -> Reader Subst (Ident, Expr -> Expr)
alphaComp avoidNames x xs = do
    let z = substFreshName avoidNames
    s <- ask
    let s' = s { inScope   = S.insert z $ S.delete x $ inScope s
               , substVar  = x
               , substExpr = Var (elemT $ typeOf xs) z
               , substFvs  = S.singleton z
               }
    pure (z, \e -> runReader (subst e) s')

alphaCompQuals :: S.Set Ident -> Ident -> Expr -> NL Qual -> Reader Subst (Ident, NL Qual, Expr -> Expr)
alphaCompQuals avoidNames x xs qs = do
    let z = substFreshName avoidNames
    s <- ask
    let s' = s { inScope   = S.insert z $ S.delete x $ inScope s
               , substVar  = x
               , substExpr = Var (elemT $ typeOf xs) z
               , substFvs  = S.singleton z
               }
    (qs', headCont) <- local (const s') (substComp qs)
    pure (z, qs', headCont)

noSubstComp :: NL Qual -> Reader Subst (NL Qual, Expr -> Expr)
noSubstComp qs = pure (qs, id)

substComp :: NL Qual -> Reader Subst (NL Qual, Expr -> Expr)
substComp (S (GuardQ p)) = do
    p' <- subst p
    s  <- ask
    pure (S (GuardQ p'), \e -> runReader (subst e) s)
substComp (S (BindQ x xs)) = do
    xs' <- subst xs
    s   <- ask
    if x == substVar s
        then pure (S (BindQ x xs'), id)
        else if x `S.member` substFvs s
                 then do
                     let avoidNames = S.unions [ inScope s
                                               , substFvs s
                                               , S.singleton $ substVar s
                                               ]
                     (z, alphaCont) <- alphaComp avoidNames x xs
                     s'             <- local (bindName z) ask
                     let substCont e = runReader (subst e) s'
                     pure (S (BindQ z xs'), substCont . alphaCont)
                 else do
                     s'             <- local (bindName x) ask
                     let substCont e = runReader (subst e) s'
                     pure (S (BindQ x xs'), substCont)
substComp (GuardQ p :* qs) = do
    p'               <- subst p
    (qs', substCont) <- substComp qs
    pure (GuardQ p' :* qs', substCont)
substComp (BindQ x xs :* qs) = do
    xs' <- subst xs
    s   <- ask
    if x == substVar s
        then pure (BindQ x xs' :* qs, id)
        else if x `S.member` substFvs s
                 then do
                     let avoidNames = S.unions [ inScope s
                                               , substFvs s
                                               , S.singleton $ substVar s
                                               , boundVarsQualsS qs
                                               ]
                     (z, qs', alphaCont) <- alphaCompQuals avoidNames x xs qs
                     (qs'', substCont)   <- local (bindName z) (substComp qs')
                     pure (BindQ z xs' :* qs'', substCont . alphaCont)
                 else do
                     (qs', substCont) <- local (bindName x) (substComp qs)
                     pure (BindQ x xs' :* qs', substCont)

subst :: Expr -> Reader Subst Expr
subst e@Table{} = pure e
subst e@Lit{}   = pure e
subst e@(Var _ x) = do
    v <- asks substVar
    if v == x
        then asks substExpr
        else pure e
subst (AppE2 ty p e1 e2) = AppE2 ty p <$> subst e1 <*> subst e2
subst (AppE1 ty p e) = AppE1 ty p <$> subst e
subst (BinOp ty p e1 e2) = BinOp ty p <$> subst e1 <*> subst e2
subst (UnOp ty p e) = UnOp ty p <$> subst e
subst (If ty e1 e2 e3) = If ty <$> subst e1 <*> subst e2 <*> subst e3
subst (MkTuple ty es) = MkTuple ty <$> mapM subst es
subst (Let ty x e1 e2) = do
    s <- ask
    e1' <- subst e1
    if x == substVar s
        then pure $ Let ty x e1' e2
        else if x `S.member` substFvs s
                 then do
                     let avoidNames = S.unions [ inScope s
                                               , substFvs s
                                               , S.singleton $ substVar s
                                               , boundVarsS e2
                                               ]
                     (z, e2') <- alphaLet avoidNames x e1 e2
                     Let ty z e1' <$> local (bindName z) (subst e2')
                 else Let ty x e1' <$> local (bindName x) (subst e2)
subst (Comp ty h qs) = do
    cont            <- asks compCont
    (qs', headCont) <- cont qs
    pure $ Comp ty (headCont h) qs'

--------------------------------------------------------------------------------
-- Tuplifying and Untuplifying variables

-- | Turn all occurences of two identifiers into accesses to one tuple variable.
-- tuplifyR z x y e = e[fst z/x][snd z/y]
tuplifyR :: Ident -> (Ident, Type) -> (Ident, Type) -> RewriteC CL
tuplifyR v (v1, t1) (v2, t2) = substR v1 v1Rep >+> substR v2 v2Rep
  where
    (v1Rep, v2Rep) = tupleVars v t1 t2

tuplifyE :: S.Set Ident -> Ident -> (Ident, Type) -> (Ident, Type) -> Expr -> Expr
tuplifyE scopeNames v (v1, t1) (v2, t2) e =
    substE scopeNames' v2 v2Rep (substE scopeNames' v1 v1Rep e)
  where
    (v1Rep, v2Rep) = tupleVars v t1 t2
    scopeNames'    = S.insert v scopeNames

tuplifyCompE :: S.Set Ident -> Ident -> (Ident, Type) -> (Ident, Type) -> NL Qual -> Expr -> (NL Qual, Expr)
tuplifyCompE scopeNames v (v1, t1) (v2, t2) qs h =
    uncurry (substCompE scopeNames' v2 v2Rep) (substCompE scopeNames' v1 v1Rep qs h)
  where
    (v1Rep, v2Rep) = tupleVars v t1 t2
    scopeNames'    = S.insert v scopeNames

tuplifyCompContE :: S.Set Ident -> Ident -> (Ident, Type) -> (Ident, Type) -> NL Qual -> (NL Qual, Expr -> Expr)
tuplifyCompContE scopeNames v (v1, t1) (v2, t2) qs = (qs'', headCont' . headCont)
  where
    (v1Rep, v2Rep)    = tupleVars v t1 t2
    scopeNames'       = S.insert v scopeNames
    (qs', headCont)   = substCompContE scopeNames' v1 v1Rep qs
    (qs'', headCont') = substCompContE scopeNames' v2 v2Rep qs'

-- | Turn all occurences of one variable into access to a tuple variable (first
-- component).
--
-- tuplifyFirstR z x y e = e[fst z/x]
tuplifyFirstR :: Ident -> (Ident, Type) -> Type -> RewriteC CL
tuplifyFirstR v (v1, t1) t2 = substR v1 v1Rep
  where
    (v1Rep, _) = tupleVars v t1 t2

-- | Turn all occurences of one variable into access to a tuple variable (second
-- component).
--
-- tuplifySecondR z x y e = e[snd z/y]
tuplifySecondR :: Ident -> Type -> (Ident, Type) -> RewriteC CL
tuplifySecondR v t1 (v2, t2) = substR v2 v2Rep
  where
    (_, v2Rep) = tupleVars v t1 t2

tupleVars :: Ident -> Type -> Type -> (Expr, Expr)
tupleVars n t1 t2 = (v1Rep, v2Rep)
  where v     = Var pt n
        pt    = PPairT t1 t2
        v1Rep = AppE1 t1 (TupElem First) v
        v2Rep = AppE1 t2 (TupElem (Next First)) v

-- | Remove tuple accessor from a variable.
unTuplifyR :: (Prim1 -> Bool) -> RewriteC CL
unTuplifyR isTupleOp = do
    AppE1 ty op (Var _ x)  <- promoteT idR
    guardM $ isTupleOp op
    return $ inject $ Var ty x

-- | Remove tuple accessor from a variable at a specific path.
unTuplifyPathR :: (Prim1 -> Bool) -> PathC -> RewriteC CL
unTuplifyPathR isTupleOp path = pathR path (unTuplifyR isTupleOp)

--------------------------------------------------------------------------------
-- Helpers for combining generators with guards in a comprehensions'
-- qualifier list

-- | Insert a guard in a qualifier list at the first possible position.
-- 'insertGuard' expects the guard expression to insert, the initial name
-- environment above the qualifiers and the list of qualifiers.
insertGuard :: Expr -> S.Set Ident -> NL Qual -> NL Qual
insertGuard guardExpr = go
  where
    go :: S.Set Ident -> NL Qual -> NL Qual
    go env (S q)                 =
        if all (`S.member` env) fvs
        then GuardQ guardExpr :* S q
        else q :* (S $ GuardQ guardExpr)
    go env (q@(BindQ x _) :* qs) =
        if all (`S.member` env) fvs
        then GuardQ guardExpr :* q :* qs
        else q :* go (S.insert x env) qs
    go env (GuardQ p :* qs)      =
        if all (`S.member` env) fvs
        then GuardQ guardExpr :* GuardQ p :* qs
        else GuardQ p :* go env qs

    fvs = freeVars guardExpr

------------------------------------------------------------------------
-- Generic iterator that merges guards into generators one by one.

-- | A container for the components of a comprehension expression
data Comp = C Type Expr (NL Qual)

fromQual :: Qual -> Either (Ident, Expr) Expr
fromQual (BindQ x e) = Left (x, e)
fromQual (GuardQ p)  = Right p


-- | Type of worker functions that merge guards into generators. It
-- receives the comprehension itself (with a qualifier list that
-- consists solely of generators), the current candidate guard
-- expression, guard expressions that have to be tried and guard
-- expressions that have been tried already. Last two are necessary if
-- the merging steps leads to tuplification.
type MergeGuard = Comp -> Expr -> [Expr] -> [Expr] -> TransformC () (Comp, [Expr], [Expr])

tryGuards :: MergeGuard  -- ^ The worker function
          -> Comp        -- ^ The current state of the comprehension
          -> [Expr]      -- ^ Guards to try
          -> [Expr]      -- ^ Guards that have been tried and failed
          -> TransformC () (Comp, [Expr])
-- Try the next guard
tryGuards mergeGuardR c (p : ps) testedGuards = do
    let tryNextGuard :: TransformC () (Comp, [Expr])
        tryNextGuard = do
            -- Try to combine p with some generators
            (comp', ps', testedGuards') <- mergeGuardR c p ps testedGuards

            -- On success, back out to give other rewrites
            -- (i.e. predicate pushdown) a chance.
            return (comp', ps' ++ testedGuards')

        -- If the current guard failed, try the next ones.
        tryOtherGuards :: TransformC () (Comp, [Expr])
        tryOtherGuards = tryGuards mergeGuardR c ps (p : testedGuards)

    tryNextGuard <+ tryOtherGuards

-- No guards left to try and none succeeded
tryGuards _ _ [] _ = fail "no predicate could be merged"

-- | Try to build flat joins (equi-, semi- and antijoins) from a
-- comprehensions qualifier list.
-- FIXME only try on those predicates that look like equi-/anti-/semi-join predicates.
-- FIXME TransformC () ... is an ugly abuse of the rewrite system
mergeGuardsIterR :: MergeGuard -> RewriteC CL
mergeGuardsIterR mergeGuardR = do
    ExprCL (Comp ty e qs) <- idR

    -- Separate generators from guards
    (g : gs, guards@(_:_)) <- return $ partitionEithers $ map fromQual $ toList qs

    let initialComp = C ty e (uncurry BindQ <$> fromListSafe g gs)

    -- Try to merge one guard with some generators
    (C _ e' qs', remGuards) <- constT (return ())
                               >>> tryGuards mergeGuardR initialComp guards []

    -- If there are any guards remaining which we could not turn into
    -- joins, append them at the end of the new qualifier list
    case remGuards of
        rg : rgs -> let rqs = GuardQ <$> fromListSafe rg rgs
                    in return $ ExprCL $ Comp ty e' (appendNL qs' rqs)
        []       -> return $ ExprCL $ Comp ty e' qs'

--------------------------------------------------------------------------------
-- Traversal functions

-- | Traverse the spine of a NL list top-down and apply the translation as soon
-- as possible.
onetdSpineT
  :: (ReadPath c Int, MonadCatch m, Walker c CL)
  => Transform c m CL b
  -> Transform c m CL b
onetdSpineT t = do
    n <- idR
    case n of
        QualsCL (_ :* _) -> childT 0 t <+ childT 1 (onetdSpineT t)
        QualsCL (S _)    -> childT 0 t
        _                -> $impossible

onetdSpineR :: (ReadPath c CrumbC, MonadCatch m, Walker c CL)
            => Rewrite c m CL
            -> Rewrite c m CL
onetdSpineR r = readerT $ \cl -> case cl of
    QualsCL _ -> r <+ childT QualsTail (onetdSpineR r)
    _         -> fail "not on spine"

--------------------------------------------------------------------------------
-- Classification of expressions

complexPrim2 :: Prim2 -> Bool
complexPrim2 _ = True

complexPrim1 :: Prim1 -> Bool
complexPrim1 op =
    case op of
        Concat    -> False
        TupElem _ -> False
        _         -> True

fromGuard :: Monad m => Qual -> m Expr
fromGuard (GuardQ e)  = return e
fromGuard (BindQ _ _) = fail "not a guard"

fromGen :: Monad m => Qual -> m (Ident, Expr)
fromGen (BindQ x xs) = return (x, xs)
fromGen (GuardQ _)   = fail "not a generator"

-- | Filtering joins are joins that only remove tuples from their left input
-- (i.e. SemiJoin, AntiJoin).
isFilteringJoin :: Monad m => Prim2 -> m (JoinPredicate ScalarExpr -> Prim2, JoinPredicate ScalarExpr)
isFilteringJoin joinOp =
    case joinOp of
        SemiJoin p -> return (SemiJoin, p)
        AntiJoin p -> return (AntiJoin, p)
        _          -> fail "not a pushable join operator"

--------------------------------------------------------------------------------
-- Fold/Group Fusion

-- | Rewrite the child expression of the aggregate into a scalar expression. The
-- identifier 'x' is the name bound by the outer comprehension.
--
-- The following forms can be rewritten:
--
-- @ x.2 @
-- @ [ f y | y <- x.2 ] @
toAggregateExprT :: Ident -> TransformC CL ScalarExpr
toAggregateExprT x =
    readerT $ \e -> case e of
        ExprCL (Comp _ _ (S (y :<-: TupSecondP _ (Var _ x')))) | x == x' ->
            childT CompHead $ promoteT (toScalarExprT y)
        ExprCL (TupSecondP t (Var _ x')) | x == x'                       ->
            return $ JInput t
        _                                                                ->
            fail "not an aggregate expression"

-- | Traverse though an expression and search for an aggregate that is eligible
-- for being merged into a NestJoin.
searchAggregatedGroupT :: Ident -> TransformC CL (PathC, AggrApp)
searchAggregatedGroupT x =
    readerT $ \e -> case e of
        ExprCL (AppE1 _ (Agg agg) _) ->
            (,) <$> (snocPathToPath <$> absPathT)
                <*> (AggrApp agg <$> childT AppE1Arg (toAggregateExprT x))
        ExprCL _      -> oneT $ searchAggregatedGroupT x
        _             -> fail "only traverse through expressions"

traverseGuardsT :: Ident -> TransformC CL a -> TransformC CL a
traverseGuardsT genName t = readerT $ \qs -> case qs of
    QualsCL (BindQ y _ :* _)
        | y == genName      -> fail "nestjoin generator name shadowed"
        | otherwise         -> childT QualsTail (traverseGuardsT genName t)
    QualsCL (GuardQ _ :* _) -> pathT [QualsHead, GuardQualExpr] t
                               <+ childT QualsTail (traverseGuardsT genName t)
    QualsCL (S (GuardQ _))  -> pathT [QualsSingleton, GuardQualExpr] t
    QualsCL (S (BindQ _ _)) -> fail "end of qualifier list"
    _                       -> fail "not a qualifier list"


--------------------------------------------------------------------------------
-- Path utilities

-- | Turn an absolute path into a local path.
localizePathT :: PathC -> TransformC CL (Path CrumbC)
localizePathT path = do
    pathLen <- length . snocPathToPath <$> absPathT
    return $ drop pathLen path

--------------------------------------------------------------------------------
-- Pattern synonyms for expressions

pattern ConcatP :: Expr -> Expr
pattern ConcatP xs <- AppE1 _ Concat xs

pattern SingletonP :: Expr -> Expr
pattern SingletonP x <- AppE1 _ Singleton x

pattern GuardP :: Expr -> Expr
pattern GuardP p <- AppE1 _ Guard p

pattern SemiJoinP :: Type -> JoinPredicate ScalarExpr -> Expr -> Expr -> Expr
pattern SemiJoinP ty p xs ys = AppE2 ty (SemiJoin p) xs ys

pattern NestJoinP :: Type -> JoinPredicate ScalarExpr -> Expr -> Expr -> Expr
pattern NestJoinP ty p xs ys = AppE2 ty (NestJoin p) xs ys

pattern GroupJoinP :: Type -> JoinPredicate ScalarExpr -> NE AggrApp -> Expr -> Expr -> Expr
pattern GroupJoinP ty p as xs ys = AppE2 ty (GroupJoin p as) xs ys

pattern GroupAggP :: Type -> NE AggrApp -> Expr -> Expr
pattern GroupAggP ty as xs = AppE1 ty (GroupAgg as) xs

pattern AndP :: Expr -> Expr
pattern AndP xs <- AppE1 _ (Agg And) xs

pattern OrP :: Expr -> Expr
pattern OrP xs <- AppE1 _ (Agg Or) xs

pattern SortP :: Type -> Expr -> Expr
pattern SortP ty xs = AppE1 ty Sort xs

pattern GroupP :: Type -> Expr -> Expr
pattern GroupP ty xs = AppE1 ty Group xs

pattern NotP :: Expr -> Expr
pattern NotP e <- UnOp _ (SUBoolOp Not) e

pattern EqP :: Expr -> Expr -> Expr
pattern EqP e1 e2 <- BinOp _ (SBRelOp Eq) e1 e2

pattern LengthP :: Expr -> Expr
pattern LengthP e <- AppE1 _ (Agg Length) e

pattern NullP :: Expr -> Expr
pattern NullP e <- AppE1 _ Null e

pattern TrueP :: Expr
pattern TrueP = Lit PBoolT (ScalarV (BoolV True))

pattern FalseP :: Expr
pattern FalseP = Lit PBoolT (ScalarV (BoolV False))

pattern TupFirstP :: Type -> Expr -> Expr
pattern TupFirstP t e = AppE1 t (TupElem First) e

pattern TupSecondP :: Type -> Expr -> Expr
pattern TupSecondP t e = AppE1 t (TupElem (Next First)) e

pattern (:<-:) :: Ident -> Expr -> Qual
pattern a :<-: b = BindQ a b

pattern LitListP :: Type -> [Val] -> Expr
pattern LitListP ty vs = Lit ty (ListV vs)

pattern SingleJoinPredP :: e -> BinRelOp -> e -> JoinPredicate e
pattern SingleJoinPredP r o l <- JoinPred (JoinConjunct r o l :| [])
