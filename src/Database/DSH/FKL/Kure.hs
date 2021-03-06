{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}

-- | Infrastructure for KURE-based rewrites on FKL expressions
module Database.DSH.FKL.Kure
    ( -- * Re-export relevant KURE modules
      module Language.KURE
    , module Language.KURE.Lens

      -- * The KURE monad
    , RewriteM, RewriteStateM, TransformF, RewriteF, LensF

      -- * Setters and getters for the translation state
    , get, put, modify, initialCtx

      -- * Changing between stateful and non-stateful transforms
    , statefulT, liftstateT

      -- * The KURE context
    , FlatCtx(..), CrumbF(..), PathF

      -- * Universes
    , FKL(..)

      -- * Congruence combinators
    , tableT, papp1T, papp2T, papp3T, binopT, unopT
    , constExprT, varT, letT

    , tableR, papp1R, papp2R, papp3R, binopR, unopR
    , constExprR, varR, letR

    , broadcastT, broadcastscalarT
    , broadcastR, broadcastscalarR

    , repT, forgetT, imprintT
    , repR, forgetR, imprintR

    , inScopeNames, freeIn, boundIn, freshNameT

    ) where


import           Control.Monad

import           Language.KURE
import           Language.KURE.Lens

import           Database.DSH.Common.Kure
import           Database.DSH.Common.Lang
import           Database.DSH.Common.Nat
import           Database.DSH.Common.Pretty
import           Database.DSH.Common.RewriteM
import           Database.DSH.Common.Type
import qualified Database.DSH.Common.VectorLang as VL
import           Database.DSH.FKL.Lang

--------------------------------------------------------------------------------
-- Convenience type aliases

type TransformF a b = Transform FlatCtx (RewriteM Int RewriteLog) a b
type RewriteF a     = TransformF a a
type LensF a b      = Lens FlatCtx (RewriteM Int RewriteLog) a b

--------------------------------------------------------------------------------

data CrumbF = AppFun
            | PApp1Arg
            | PApp2Arg1
            | PApp2Arg2
            | PApp3Arg1
            | PApp3Arg2
            | PApp3Arg3
            | BinOpArg1
            | BinOpArg2
            | UnOpArg
            | ImprintArg1
            | ImprintArg2
            | RepArg
            | ForgetArg
            | BroadcastScalarArg
            | BroadcastArg1
            | BroadcastArg2
            | BroadcastLArg1
            | BroadcastLArg2
            | LetBind
            | LetBody
            | TupleElem Int
            | ExtExpr
            deriving (Eq, Show)

type AbsPathF = AbsolutePath CrumbF

type PathF = Path CrumbF

-- | The context for KURE-based FKL rewrites
data FlatCtx = FlatCtx { fklPath     :: AbsPathF
                       , fklBindings :: [Ident]
                       }

instance ExtendPath FlatCtx CrumbF where
    c@@n = c { fklPath = fklPath c @@ n }

instance ReadPath FlatCtx CrumbF where
    absPath = fklPath

initialCtx :: FlatCtx
initialCtx = FlatCtx { fklPath = mempty, fklBindings = [] }

-- | Record a variable binding in the context
bindVar :: Ident -> FlatCtx -> FlatCtx
bindVar n ctx = ctx { fklBindings = n : fklBindings ctx }

inScopeNames :: FlatCtx -> [Ident]
inScopeNames = fklBindings

boundIn :: Ident -> FlatCtx -> Bool
boundIn n ctx = n `elem` fklBindings ctx

freeIn :: Ident -> FlatCtx -> Bool
freeIn n ctx = n `notElem` fklBindings ctx

-- | Generate a fresh name that is not bound in the current context.
freshNameT :: [Ident] -> TransformF a Ident
freshNameT avoidNames = do
    ctx <- contextT
    constT $ freshName (avoidNames ++ inScopeNames ctx)

--------------------------------------------------------------------------------
-- Support for stateful transforms

-- | Run a stateful transform with an initial state and turn it into a regular
-- (non-stateful) transform
statefulT :: s -> Transform FlatCtx (RewriteStateM s RewriteLog) a b -> TransformF a (s, b)
statefulT s = resultT (stateful s)

-- | Turn a regular rewrite into a stateful rewrite
liftstateT :: Transform FlatCtx (RewriteM Int RewriteLog) a b -> Transform FlatCtx (RewriteStateM s RewriteLog) a b
liftstateT = resultT liftstate

--------------------------------------------------------------------------------
-- Congruence combinators for FKL lexpressions

tableT :: Monad m => (Type -> String -> BaseTableSchema -> b)
                  -> Transform FlatCtx m (ExprTempl l e) b
tableT f = contextfreeT $ \expr -> case expr of
                      Table ty n schema -> return $ f ty n schema
                      _                 -> fail "not a table node"
{-# INLINE tableT #-}


tableR :: Monad m => Rewrite FlatCtx m (ExprTempl l e)
tableR = tableT Table
{-# INLINE tableR #-}

binopT :: Monad m => Transform FlatCtx m (ExprTempl l e) a1
                  -> Transform FlatCtx m (ExprTempl l e) a2
                  -> (Type -> ScalarBinOp -> l -> a1 -> a2 -> b)
                  -> Transform FlatCtx m (ExprTempl l e) b
binopT t1 t2 f = transform $ \c expr -> case expr of
                     BinOp ty op l e1 e2 -> f ty op l <$> applyT t1 (c@@BinOpArg1) e1 <*> applyT t2 (c@@BinOpArg2) e2
                     _                   -> fail "not a binary operator application"
{-# INLINE binopT #-}

binopR :: Monad m => Rewrite FlatCtx m (ExprTempl l e) -> Rewrite FlatCtx m (ExprTempl l e) -> Rewrite FlatCtx m (ExprTempl l e)
binopR t1 t2 = binopT t1 t2 BinOp
{-# INLINE binopR #-}

unopT :: Monad m => Transform FlatCtx m (ExprTempl l e) a
                 -> (Type -> ScalarUnOp -> l -> a -> b)
                 -> Transform FlatCtx m (ExprTempl l e) b
unopT t f = transform $ \ctx expr -> case expr of
                     UnOp ty op l e -> f ty op l <$> applyT t (ctx@@UnOpArg) e
                     _              -> fail "not an unary operator application"
{-# INLINE unopT #-}

unopR :: Monad m => Rewrite FlatCtx m (ExprTempl l e) -> Rewrite FlatCtx m (ExprTempl l e)
unopR t = unopT t UnOp
{-# INLINE unopR #-}

papp1T :: Monad m => Transform FlatCtx m (ExprTempl l e) a
                  -> (Type -> Prim1 -> l -> a -> b)
                  -> Transform FlatCtx m (ExprTempl l e) b
papp1T t f = transform $ \c expr -> case expr of
                      PApp1 ty p l e -> f ty p l <$> applyT t (c@@PApp1Arg) e
                      _              -> fail "not a unary primitive application"
{-# INLINE papp1T #-}

papp1R :: Monad m => Rewrite FlatCtx m (ExprTempl l e) -> Rewrite FlatCtx m (ExprTempl l e)
papp1R t = papp1T t PApp1
{-# INLINE papp1R #-}

papp2T :: Monad m => Transform FlatCtx m (ExprTempl l e) a1
                  -> Transform FlatCtx m (ExprTempl l e) a2
                  -> (Type -> Prim2 -> l -> a1 -> a2 -> b)
                  -> Transform FlatCtx m (ExprTempl l e) b
papp2T t1 t2 f = transform $ \c expr -> case expr of
                     PApp2 ty p l e1 e2 -> f ty p l <$> applyT t1 (c@@PApp2Arg1) e1 <*> applyT t2 (c@@PApp2Arg2) e2
                     _                  -> fail "not a binary primitive application"
{-# INLINE papp2T #-}

papp2R :: Monad m => Rewrite FlatCtx m (ExprTempl l e) -> Rewrite FlatCtx m (ExprTempl l e) -> Rewrite FlatCtx m (ExprTempl l e)
papp2R t1 t2 = papp2T t1 t2 PApp2
{-# INLINE papp2R #-}

papp3T :: Monad m => Transform FlatCtx m (ExprTempl l e) a1
                  -> Transform FlatCtx m (ExprTempl l e) a2
                  -> Transform FlatCtx m (ExprTempl l e) a3
                  -> (Type -> Prim3 -> l -> a1 -> a2 -> a3 -> b)
                  -> Transform FlatCtx m (ExprTempl l e) b
papp3T t1 t2 t3 f = transform $ \c expr -> case expr of
                     PApp3 ty p l e1 e2 e3 -> f ty p l
                                              <$> applyT t1 (c@@PApp3Arg1) e1
                                              <*> applyT t2 (c@@PApp3Arg2) e2
                                              <*> applyT t3 (c@@PApp3Arg3) e3
                     _                     -> fail "not a ternary primitive application"
{-# INLINE papp3T #-}

papp3R :: Monad m
       => Rewrite FlatCtx m (ExprTempl l e)
       -> Rewrite FlatCtx m (ExprTempl l e)
       -> Rewrite FlatCtx m (ExprTempl l e)
       -> Rewrite FlatCtx m (ExprTempl l e)
papp3R t1 t2 t3 = papp3T t1 t2 t3 PApp3
{-# INLINE papp3R #-}

constExprT :: Monad m => (Type -> [Val] -> b) -> Transform FlatCtx m (ExprTempl l e) b
constExprT f = contextfreeT $ \expr -> case expr of
                    Const ty v -> return $ f ty v
                    _          -> fail "not a constant"
{-# INLINE constExprT #-}

constExprR :: Monad m => Rewrite FlatCtx m (ExprTempl l e)
constExprR = constExprT Const
{-# INLINE constExprR #-}

letT :: Monad m => Transform FlatCtx m (ExprTempl l e) a1
                -> Transform FlatCtx m (ExprTempl l e) a2
                -> (Type -> Ident -> a1 -> a2 -> b)
                -> Transform FlatCtx m (ExprTempl l e) b
letT t1 t2 f = transform $ \c expr -> case expr of
                 Let ty x xs e -> f ty x <$> applyT t1 (c@@LetBind) xs
                                         <*> applyT t2 (bindVar x $ c@@LetBody) e
                 _             -> fail "not a let expression"
{-# INLINE letT #-}

letR :: Monad m => Rewrite FlatCtx m (ExprTempl l e)
                -> Rewrite FlatCtx m (ExprTempl l e)
                -> Rewrite FlatCtx m (ExprTempl l e)
letR r1 r2 = letT r1 r2 Let
{-# INLINE letR #-}

varT :: Monad m => (Type -> Ident -> b) -> Transform FlatCtx m (ExprTempl l e) b
varT f = contextfreeT $ \expr -> case expr of
             Var ty n -> return $ f ty n
             _        -> fail "not a variable"
{-# INLINE varT #-}

varR :: Monad m => Rewrite FlatCtx m (ExprTempl l e)
varR = varT Var
{-# INLINE varR #-}

mkTupleT :: Monad m => Transform FlatCtx m (ExprTempl l e) a
                    -> (Type -> l -> [a] -> b)
                    -> Transform FlatCtx m (ExprTempl l e) b
mkTupleT t f = transform $ \c expr -> case expr of
                   MkTuple ty l es -> f ty l <$> zipWithM (\e i -> applyT t (c@@TupleElem i) e) es [1..]
                   _               -> fail "not a tuple constructor"
{-# INLINE mkTupleT #-}

mkTupleR :: Monad m => Rewrite FlatCtx m (ExprTempl l e) -> Rewrite FlatCtx m (ExprTempl l e)
mkTupleR r = mkTupleT r MkTuple

extT :: Monad m => Transform FlatCtx m e a
                -> (a -> b)
                -> Transform FlatCtx m (ExprTempl l e) b
extT t f = transform $ \c expr -> case expr of
    Ext e -> f <$> applyT t (c@@ExtExpr) e
    _     -> fail "not an extension mode"
{-# INLINE extT #-}


extR :: Monad m => Rewrite FlatCtx m e -> Rewrite FlatCtx m (ExprTempl l e)
extR r = extT r Ext
{-# INLINE extR #-}

--------------------------------------------------------------------------------

repT :: Monad m => Transform FlatCtx m FExpr a
                -> (Type -> VL.VecVal -> a -> b)
                -> Transform FlatCtx m ShapeExt b
repT t f = transform $ \c expr -> case expr of
                        Rep ty v e -> f ty v <$> applyT t (c@@RepArg) e
                        _          -> fail "not a rep application"
{-# INLINE repT #-}

repR :: Monad m => Rewrite FlatCtx m FExpr -> Rewrite FlatCtx m ShapeExt
repR r = repT r Rep
{-# INLINE repR #-}

forgetT :: Monad m => Transform FlatCtx m FExpr a
                   -> (Nat -> Type -> a -> b)
                   -> Transform FlatCtx m ShapeExt b
forgetT t f = transform $ \c expr -> case expr of
                        Forget n ty e -> f n ty <$> applyT t (c@@ForgetArg) e
                        _             -> fail "not a forget application"
{-# INLINE forgetT #-}

forgetR :: Monad m => Rewrite FlatCtx m FExpr -> Rewrite FlatCtx m ShapeExt
forgetR t = forgetT t Forget
{-# INLINE forgetR #-}

imprintT :: Monad m => Transform FlatCtx m FExpr a1
                    -> Transform FlatCtx m FExpr a2
                    -> (Nat -> Type -> a1 -> a2 -> b)
                    -> Transform FlatCtx m ShapeExt b
imprintT t1 t2 f = transform $ \c expr -> case expr of
                     Imprint n ty e1 e2 -> f n ty <$> applyT t1 (c@@ImprintArg1) e1
                                                  <*> applyT t2 (c@@ImprintArg2) e2
                     _                  -> fail "not a imprint call"
{-# INLINE imprintT #-}

imprintR :: Monad m => Rewrite FlatCtx m FExpr -> Rewrite FlatCtx m FExpr -> Rewrite FlatCtx m ShapeExt
imprintR t1 t2 = imprintT t1 t2 Imprint
{-# INLINE imprintR #-}

--------------------------------------------------------------------------------

broadcastT :: Monad m => Transform FlatCtx m LExpr a1
                      -> Transform FlatCtx m LExpr a2
                      -> (Nat -> Type -> a1 -> a2 -> b)
                      -> Transform FlatCtx m BroadcastExt b
broadcastT t1 t2 f = transform $ \c expr -> case expr of
    Broadcast n ty e1 e2 -> f n ty <$> applyT t1 (c@@BroadcastArg1) e1
                                   <*> applyT t2 (c@@BroadcastArg2) e2
    _                    -> fail "not a broadcast call"
{-# INLINE broadcastT #-}

broadcastR :: Monad m => Rewrite FlatCtx m LExpr
                      -> Rewrite FlatCtx m LExpr
                      -> Rewrite FlatCtx m BroadcastExt
broadcastR r1 r2 = broadcastT r1 r2 Broadcast
{-# INLINE broadcastR #-}

broadcastscalarT :: Monad m => Transform FlatCtx m LExpr a
                            -> (Nat -> Type -> VL.VecVal -> a -> b)
                            -> Transform FlatCtx m BroadcastExt b
broadcastscalarT t f = transform $ \c expr -> case expr of
    BroadcastScalar n ty v e -> f n ty v <$> applyT t (c@@BroadcastScalarArg) e
    _                        -> fail "not a broadcastscalar call"
{-# INLINE broadcastscalarT #-}

broadcastscalarR :: Monad m => Rewrite FlatCtx m LExpr
                            -> Rewrite FlatCtx m BroadcastExt
broadcastscalarR r = broadcastscalarT r BroadcastScalar
{-# INLINE broadcastscalarR #-}

--------------------------------------------------------------------------------

data FKL l e = ExprFKL (ExprTempl l e)
             | ExtFKL e

instance (Pretty e, Pretty l) => Pretty (FKL l e) where
    pretty (ExprFKL e) = pretty e
    pretty (ExtFKL o)  = pretty o

instance Injection FExpr (FKL Lifted ShapeExt) where
    inject              = ExprFKL

    project (ExprFKL e) = Just e
    project _           = Nothing

instance Injection ShapeExt (FKL Lifted ShapeExt) where
    inject             = ExtFKL

    project (ExtFKL s) = Just s
    project _          = Nothing

--------------------------------------------------------------------------------

instance Injection LExpr (FKL LiftedN BroadcastExt) where
    inject              = ExprFKL

    project (ExprFKL e) = Just e
    project _           = Nothing

instance Injection BroadcastExt (FKL LiftedN BroadcastExt) where
    inject             = ExtFKL

    project (ExtFKL s) = Just s
    project _          = Nothing


--------------------------------------------------------------------------------

instance Walker FlatCtx (FKL Lifted ShapeExt) where
    allR r =
        rewrite $ \c fkl -> case fkl of
            ExprFKL expr -> inject <$> applyT (allRExpr r) c expr
            ExtFKL o     -> inject <$> applyT allRShape c o

      where
        allRShape = readerT $ \o -> case o of
                Rep{}     -> repR (extractR r)
                Imprint{} -> imprintR (extractR r) (extractR r)
                Forget{}  -> forgetR (extractR r)

instance Walker FlatCtx (FKL LiftedN BroadcastExt) where
    allR r =
        rewrite $ \c fkl -> case fkl of
            ExprFKL expr -> inject <$> applyT (allRExpr r) c expr
            ExtFKL o     -> inject <$> applyT allRBC c o

      where
        allRBC = readerT $ \o -> case o of
                Broadcast{}        -> broadcastR (extractR r) (extractR r)
                BroadcastScalar{}  -> broadcastscalarR  (extractR r)

allRExpr :: (Injection (ExprTempl t t1) g, Injection t1 g, Monad m)
         => Rewrite FlatCtx m g
         -> Transform FlatCtx m (ExprTempl t t1) (ExprTempl t t1)
allRExpr r = readerT $ \e -> case e of
        Table{}   -> idR
        PApp1{}   -> papp1R (extractR r)
        PApp2{}   -> papp2R (extractR r) (extractR r)
        PApp3{}   -> papp3R (extractR r) (extractR r) (extractR r)
        BinOp{}   -> binopR (extractR r) (extractR r)
        UnOp{}    -> unopR (extractR r)
        Const{}   -> idR
        Let{}     -> letR (extractR r) (extractR r)
        Var{}     -> idR
        MkTuple{} -> mkTupleR (extractR r)
        Ext{}     -> extR (extractR r)
