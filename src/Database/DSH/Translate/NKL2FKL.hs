{-# LANGUAGE TemplateHaskell #-}
-- | The Flattening Transformation
module Database.DSH.Translate.NKL2FKL
    ( flatTransform
    , normalizeLifted
    , liftOperators
    ) where

-- FIXME use more let bindings to avoid term replication, e.g. in if conditionals
-- FIXME make sure that no wrong shadowing occurs while lifting or restricting the environment.

import           Control.Monad.State
import           Control.Monad.Reader

import           Database.DSH.Common.Impossible
import           Database.DSH.Common.Lang
import           Database.DSH.Common.Nat
import           Database.DSH.Common.Type
import qualified Database.DSH.FKL.Lang       as F
import qualified Database.DSH.FKL.Primitives as P
import           Database.DSH.FKL.Rewrite
import qualified Database.DSH.NKL.Lang       as N

-- | Transform an expression in the Nested Kernel Language into its
-- equivalent Flat Kernel Language expression by means of the
-- flattening transformation. Apply standard optimization rewrites.
flatTransform :: N.Expr -> F.FExpr
flatTransform expr = optimizeNormFKL
                     $ normalizeLifted
                     $ optimizeFKL
                     $ runFlat initEnv (flatten expr)

--------------------------------------------------------------------------------
-- The Flattening Transformation

-- | The first stage of the flattening transformation: replace
-- iterators by lifted operators.
liftOperators :: N.Expr -> F.LExpr
liftOperators expr = runFlat initEnv (flatten expr)

--------------------------------------------------------------------------------
-- Translation of built-in combinators. Combinators are lifted
-- according to the iteration depth at which they are encountered.

prim1 :: N.Prim1 -> F.LExpr -> Nat -> F.LExpr
prim1 p =
    case p of
        N.Singleton -> P.sng
        N.Only      -> P.only
        N.Length    -> P.length
        N.Concat    -> P.concat
        N.Sum       -> P.sum
        N.Avg       -> P.avg
        N.TupElem n -> P.tupElem n
        N.Minimum   -> P.minimum
        N.Maximum   -> P.maximum
        N.Reverse   -> P.reverse
        N.And       -> P.and
        N.Or        -> P.or
        N.Nub       -> P.nub
        N.Number    -> P.number
        N.Sort      -> P.sort
        N.Group     -> P.group
        N.Restrict  -> P.restrict

prim2 :: N.Prim2 -> F.LExpr -> F.LExpr -> Nat -> F.LExpr
prim2 p =
    case p of
        N.Append       -> P.append
        N.Zip          -> P.zip
        N.CartProduct  -> P.cartProduct
        N.NestProduct  -> P.nestProduct
        N.ThetaJoin jp -> P.thetaJoin jp
        N.NestJoin jp  -> P.nestJoin jp
        N.SemiJoin jp  -> P.semiJoin jp
        N.AntiJoin jp  -> P.antiJoin jp

--------------------------------------------------------------------------------
-- Flattening environment

type Flatten a = Reader Env a

runFlat :: Env -> Flatten a -> a
runFlat env ma = runReader ma env

envVar :: (Ident, Type) -> F.LExpr
envVar (n, t) = F.Var t n

-- | The environment stores all variables which are currently in scope and the current iteration depth.
data Env = Env
    { -- | All bindings which are currently in scope and need to be
      -- lifted to the current iteration context.
      inScope    :: [(Ident, Type)]

      -- | The current iteration depth
    , frameDepth :: Nat
    }

initEnv :: Env
initEnv = Env { inScope = [], frameDepth = Zero }

bindEnv :: Ident -> Type -> Env -> Env
bindEnv n t e = e { inScope = (n, t) : inScope e }

-- | Update the environment to express the descent into a
-- comprehension that binds the name 'x'. This involves binding 'x' in
-- the current environment frame and increasing the frame depth.
descendEnv :: (Ident, Type) -> Env -> Env
descendEnv x env = env { inScope    = x : inScope env
                       , frameDepth = Succ $ frameDepth env
                       }

frameDepthM :: Flatten Nat
frameDepthM = asks frameDepth

-- | Restrict all environment entries according to a boolean vector
-- ('then' or 'else' branch).
restrictEnv :: [(Ident, Type)] -> Nat -> F.LExpr -> F.LExpr -> F.LExpr
restrictEnv env d1 bs branchExpr = mkRestrictLet env
  where
    mkRestrictLet :: [(Ident, Type)] -> F.LExpr
    mkRestrictLet [] = $impossible
    mkRestrictLet (e : []) =
        P.let_ (fst e)
               (P.restrict (P.tuple [envVar e, bs] (Succ d1)) d1)
               branchExpr
    mkRestrictLet (e : (e2 : es)) =
        P.let_ (fst e)
               (P.restrict (P.tuple [envVar e, bs] (Succ d1)) d1)
               (mkRestrictLet (e2 : es))

-- | Lift all names bound in the environment: the value is replicated
-- for each element of the current context. The chain of 'let's is
-- terminated by the flattened head expression of the current
-- iterator.
liftEnv :: (Ident, Type) -> Nat -> F.LExpr -> [(Ident, Type)] -> F.LExpr
liftEnv ctx d headExpr env = mkLiftingLet env
  where
    mkLiftingLet :: [(Ident, Type)] -> F.LExpr
    mkLiftingLet []        = headExpr
    mkLiftingLet (e : [])  =
        P.let_ (fst e) (P.dist (envVar e) cv d) headExpr
    mkLiftingLet (e : (e2 : es)) =
        P.let_ (fst e) (P.dist (envVar e) cv d) (mkLiftingLet (e2 : es))

    cv :: F.LExpr
    cv = envVar ctx


--------------------------------------------------------------------------------

-- | Transform top-level expressions which are not nested in an
-- iterator.
flatten :: N.Expr -> Flatten F.LExpr
flatten (N.Table t n schema) = return $ F.Table t n schema
flatten (N.UnOp t op e1)     = P.un t op <$> flatten e1 <*> pure Zero
flatten (N.BinOp t op e1 e2) = P.bin t op <$> flatten e1 <*> flatten e2 <*> pure Zero
flatten (N.Const t v)        = return $ F.Const t v
flatten (N.Var t v)          = return $ F.Var t v
flatten (N.If t ce te ee)    = F.If t <$> flatten ce <*> flatten te <*> flatten ee
flatten (N.AppE1 _ p e)      = prim1 p <$> flatten e <*> pure Zero
flatten (N.AppE2 _ p e1 e2)  = prim2 p <$> flatten e1 <*> flatten e2 <*> pure Zero
flatten (N.Let _ x xs e)     = P.let_ x <$> flatten xs <*> local (bindEnv x (typeOf xs)) (flatten e)
flatten (N.MkTuple _ es)     = P.tuple <$> mapM flatten es <*> pure Zero
flatten (N.Iterator _ h x xs)    = do
    -- Prepare an environment in which the current generator is the
    -- context
    let initCtx    = (x, typeOf xs)

    -- In this environment, transform the iterator head
    flatHead <- local (descendEnv initCtx) (deepFlatten initCtx h)

    P.let_ x <$> flatten xs <*> (liftEnv initCtx Zero flatHead <$> asks inScope)

--------------------------------------------------------------------------------

-- | Compile expressions nested in an iterator.
deepFlatten :: (Ident, Type) -> N.Expr -> Flatten F.LExpr
deepFlatten _   (N.Var t v)          = frameDepthM >>= \d -> return $ F.Var (liftTypeN d t) v
deepFlatten ctx (N.Table t n schema) = P.broadcast (F.Table t n schema) (envVar ctx) <$> frameDepthM
deepFlatten ctx (N.Const t v)        = P.broadcast (F.Const t v) (envVar ctx) <$> frameDepthM
deepFlatten ctx (N.UnOp t op e1)     = P.un t op <$> deepFlatten ctx e1 <*> frameDepthM
deepFlatten ctx (N.BinOp t op e1 e2) = P.bin t op <$> deepFlatten ctx e1 <*> deepFlatten ctx e2 <*> frameDepthM
deepFlatten ctx (N.MkTuple _ es)     = frameDepthM >>= \d -> P.tuple <$> mapM (deepFlatten ctx) es <*> pure d
deepFlatten ctx (N.AppE1 _ p e)      = prim1 p <$> deepFlatten ctx e <*> frameDepthM
deepFlatten ctx (N.AppE2 _ p e1 e2)  = prim2 p <$> deepFlatten ctx e1 <*> deepFlatten ctx e2 <*> frameDepthM

deepFlatten ctx (N.Let _ x xs e)     = P.let_ x <$> deepFlatten ctx xs
                                                <*> local (bindEnv x (typeOf xs)) (deepFlatten ctx e)

deepFlatten ctx (N.If _ ce te ee)    = do
    Succ d1      <- frameDepthM

    -- Lift the condition
    bs           <- deepFlatten ctx ce

    -- Lift the THEN branch. Note that although the environment record
    -- does not change, all environment variables are re-bound to a
    -- restricted environment by 'restrictEnv'.
    thenExpr     <- deepFlatten ctx te

    -- Lift the ELSE branch. See comment above.
    elseExpr     <- deepFlatten ctx ee

    env          <- asks inScope

    -- Construct the restricted environments in which the THEN and
    -- ELSE branches are evaluated.
    let notL xs = P.un PBoolT (SUBoolOp Not) xs (Succ d1)

        thenRes = restrictEnv env d1 bs thenExpr

        elseRes = restrictEnv env d1 (notL bs) elseExpr

    return $ P.combine bs thenRes elseRes d1

-- FIXME lift types in the environment (add one list type constructor)
deepFlatten ctx (N.Iterator _ h x xs)    = do
    d           <- frameDepthM
    env         <- asks inScope
    let ctx' = (x, liftTypeN (Succ d) (typeOf xs))
    headExpr    <- local (descendEnv ctx') $ deepFlatten ctx' h

    xs'         <- deepFlatten ctx xs

    return $ P.let_ x xs' (liftEnv ctx' d headExpr env)


--------------------------------------------------------------------------------
-- Normalization of intermediate flat expressions into the final
-- form. This step eliminates higher-lifted occurences of built-in
-- combinators.

type Supply = Int

type NormFlat a = State Supply a

freshNameN :: NormFlat Ident
freshNameN = do
    i <- get
    put $ i + 1
    return $ "nf" ++ show i

normalizeLifted :: F.LExpr -> F.FExpr
normalizeLifted e = evalState (normLifting e) 0

implementBroadcast :: F.BroadcastExt -> NormFlat F.FExpr
implementBroadcast (F.Broadcast d _ e1 e2) = do
    e1' <- normLifting e1
    e2' <- normLifting e2
    case d of
        Zero             -> $impossible
        Succ Zero        -> return $ P.fdist e1' e2'
        -- FIXME use let-binding
        Succ d1@(Succ _) -> return $ P.imprint d1 e2' (P.fdist e1' (P.forget d1 e2'))

-- | Reduce all higher-lifted occurences of primitive combinators and
-- operators to singly lifted variants by flattening the arguments and
-- restoring the original list shape on the result.
normLifting :: F.LExpr -> NormFlat F.FExpr
normLifting (F.Table t n schema)   = return $ F.Table t n schema
normLifting (F.If t ce te ee)      = F.If t <$> normLifting ce <*> normLifting te <*> normLifting ee
normLifting (F.Const t v)          = return $ F.Const t v
normLifting (F.Var t n)            = return $ F.Var t n
normLifting (F.Let t x e1 e2)      = F.Let t x <$> normLifting e1 <*> normLifting e2
normLifting (F.Ext b)              = implementBroadcast b
normLifting (F.MkTuple t l es)     =
    case l of
        F.LiftedN Zero         -> F.MkTuple t F.NotLifted <$> mapM normLifting es
        F.LiftedN (Succ Zero)  -> F.MkTuple t F.Lifted <$> mapM normLifting es
        F.LiftedN (Succ d)     -> do
            e1' : es' <- mapM normLifting es
            n         <- freshNameN
            let v   = F.Var (typeOf e1') n
                app = F.MkTuple (unliftTypeN d t) F.Lifted (P.forget d v : map (P.forget d) es')
            return $ P.let_ n e1' $ P.imprint d v app

normLifting (F.UnOp t op l e)      =
    case l of
        F.LiftedN Zero         -> F.UnOp t op F.NotLifted <$> normLifting e
        F.LiftedN (Succ Zero)  -> F.UnOp t op F.Lifted <$> normLifting e
        F.LiftedN (Succ d)     -> do
            e' <- normLifting e
            n  <- freshNameN
            let v   = F.Var (typeOf e') n
                app = F.UnOp (unliftTypeN d t) op F.Lifted (P.forget d v)
            return $ P.let_ n e' $ P.imprint d v app

normLifting (F.BinOp t op l e1 e2)  =
    case l of
        F.LiftedN Zero         -> F.BinOp t op F.NotLifted
                                            <$> normLifting e1
                                            <*> normLifting e2
        F.LiftedN (Succ Zero)  -> F.BinOp t op F.Lifted
                                            <$> normLifting e1
                                            <*> normLifting e2
        F.LiftedN (Succ d)     -> do
            e1' <- normLifting e1
            e2' <- normLifting e2
            n   <- freshNameN
            let v   = F.Var (typeOf e1') n
                app = F.BinOp (unliftTypeN d t) op F.Lifted (P.forget d v) (P.forget d e2')
            return $ P.let_ n e1' $ P.imprint d v app

normLifting (F.PApp1 t p l e)    =
    case l of
        F.LiftedN Zero         -> F.PApp1 t p F.NotLifted <$> normLifting e
        F.LiftedN (Succ Zero)  -> F.PApp1 t p F.Lifted <$> normLifting e
        F.LiftedN (Succ d)     -> do
            e' <- normLifting e
            n  <- freshNameN
            let v   = F.Var (typeOf e') n
                app = F.PApp1 (unliftTypeN d t) p F.Lifted (P.forget d v)
            return $ P.let_ n e' (P.imprint d v app)

normLifting (F.PApp2 t p l e1 e2)   =
    case l of
        F.LiftedN Zero         -> F.PApp2 t p F.NotLifted
                                              <$> normLifting e1
                                              <*> normLifting e2
        F.LiftedN (Succ Zero)  -> F.PApp2 t p F.Lifted
                                              <$> normLifting e1
                                              <*> normLifting e2
        F.LiftedN (Succ d)     -> do
            e1' <- normLifting e1
            e2' <- normLifting e2
            n   <- freshNameN
            let v   = F.Var (typeOf e1') n
                app = F.PApp2 (unliftTypeN d t) p F.Lifted (P.forget d v) (P.forget d e2')
            return $ P.let_ n e1' $ P.imprint d v app

normLifting (F.PApp3 t p l e1 e2 e3)    =
    case l of
        F.LiftedN Zero        -> F.PApp3 t p F.NotLifted
                                             <$> normLifting e1
                                             <*> normLifting e2
                                             <*> normLifting e3
        F.LiftedN (Succ Zero) -> F.PApp3 t p F.Lifted
                                             <$> normLifting e1
                                             <*> normLifting e2
                                             <*> normLifting e3
        F.LiftedN (Succ d)    -> do
            e1' <- normLifting e1
            e2' <- normLifting e2
            e3' <- normLifting e3
            n   <- freshNameN
            let v   = F.Var (typeOf e1') n
                app = F.PApp3 (unliftTypeN d t) p F.Lifted (P.forget d v)
                                                           (P.forget d e2')
                                                           (P.forget d e3')
            return $ P.let_ n e1' $ P.imprint d v app
