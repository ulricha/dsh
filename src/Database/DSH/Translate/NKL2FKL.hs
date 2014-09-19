{-# LANGUAGE TemplateHaskell #-}
-- | The Flattening Transformation
module Database.DSH.Translate.NKL2FKL (flatTransform) where

-- FIXME use more let bindings to avoid term replication, e.g. in if conditionals
-- FIXME make sure that no wrong shadowing occurs while lifting or restricting the environment.

#ifdef DEBUGCOMP
import           Debug.Trace
import           Database.DSH.Common.Pretty
#endif

import           Control.Monad.State
import           Control.Monad.Reader
import           Control.Applicative

import           Database.DSH.Common.Lang
import           Database.DSH.Common.Nat
import           Database.DSH.Common.Type
import qualified Database.DSH.FKL.Lang       as F
import qualified Database.DSH.FKL.Primitives as P
import qualified Database.DSH.NKL.Lang       as N

-- | Transform an expression in the Nested Kernel Language into its
-- equivalent Flat Kernel Language expression by means of the
-- flattening transformation.
flatTransform :: N.Expr -> F.FExpr
flatTransform expr = 
#ifdef DEBUGCOMP
    let lexpr = flatten expr
        fexpr = normalize lexpr
    in trace (decorate "Flattened" lexpr) $
       trace (decorate "Normalized Flat" fexpr) $
       fexpr

  where
    padSep :: String -> String
    padSep s = "\n" ++ s ++ " " ++ replicate (100 - length s) '=' ++ "\n"

    decorate :: Pretty e => String -> e -> String
    decorate msg e = padSep msg ++ pp e ++ padSep ""
    
#else
    normalize $ flatten expr
#endif

--------------------------------------------------------------------------------
-- The Flattening Transformation

--------------------------------------------------------------------------------
-- Translation of built-in combinators. Combinators are lifted
-- according to the iteration depth at which they are encountered.

prim1 :: N.Prim1 Type -> F.LExpr -> Nat -> F.LExpr
prim1 (N.Prim1 p _) =
    case p of
        N.Length    -> P.length
        N.Concat    -> P.concat
        N.Sum       -> P.sum
        N.Avg       -> P.avg
        N.The       -> P.the
        N.Fst       -> P.fst
        N.Snd       -> P.snd
        N.Head      -> P.head
        N.Tail      -> P.tail
        N.Minimum   -> P.minimum
        N.Maximum   -> P.maximum
        N.Reverse   -> P.reverse
        N.And       -> P.and
        N.Or        -> P.or
        N.Init      -> P.init
        N.Last      -> P.last
        N.Nub       -> P.nub
        N.Number    -> P.number
        N.Reshape n -> P.reshape n
        N.Transpose -> P.transpose

prim2 :: N.Prim2 Type -> F.LExpr -> F.LExpr -> Nat -> F.LExpr
prim2 (N.Prim2 p _) =
    case p of
        N.Group        -> P.group
        N.Sort         -> P.sort
        N.Restrict     -> P.restrict
        N.Pair         -> P.pair
        N.Append       -> P.append
        N.Index        -> P.index
        N.Zip          -> P.zip
        N.Cons         -> P.cons
        N.CartProduct  -> P.cartProduct
        N.NestProduct  -> P.nestProduct
        N.ThetaJoin jp -> P.thetaJoin jp
        N.NestJoin jp  -> P.nestJoin jp
        N.SemiJoin jp  -> P.semiJoin jp
        N.AntiJoin jp  -> P.antiJoin jp

--------------------------------------------------------------------------------

-- | Transform top-level expressions which are not nested in a
-- comprehension.  
flatten :: N.Expr -> F.LExpr
flatten (N.Table t n cs hs)  = F.Table t n cs hs
flatten (N.UnOp t op e1)     = P.un t op (flatten e1) Zero
flatten (N.BinOp t op e1 e2) = P.bin t op (flatten e1) (flatten e2) Zero
flatten (N.Const t v)        = F.Const t v
flatten (N.Var t v)          = F.Var t v
flatten (N.If t ce te ee)    = F.If t (flatten ce) (flatten te) (flatten ee)
flatten (N.AppE1 _ p e)      = prim1 p (flatten e) Zero
flatten (N.AppE2 _ p e1 e2)  = prim2 p (flatten e1) (flatten e2) Zero
flatten (N.Comp _ h x xs)    = P.let_ x (flatten xs) (topFlatten (x, typeOf xs) h)
flatten (N.Let _ x xs e)     = P.let_ x (flatten xs) (flatten e)

--------------------------------------------------------------------------------

-- | Compile expressions nested in the top-most comprehension (with
-- iteration depth 1).
topFlatten :: (Ident, Type) -> N.Expr -> F.LExpr
topFlatten ctx (N.Table t n cs hs)  = P.dist (F.Table t n cs hs) (envVar ctx)
topFlatten ctx (N.UnOp t op e1)     = P.un t op (topFlatten ctx e1) (Succ Zero)
topFlatten ctx (N.BinOp t op e1 e2) = P.bin t op (topFlatten ctx e1) (topFlatten ctx e2) (Succ Zero)
topFlatten ctx (N.Const t v)        = P.dist (F.Const t v) (envVar ctx)
topFlatten _   (N.Var t v)          = F.Var (liftType t) v
topFlatten ctx (N.Let _ x xs e)     = P.let_ x (topFlatten ctx xs) (topFlatten ctx e)
topFlatten ctx (N.If _ ce te ee)    =
    -- Combine the results for the then and else branches. Combined,
    -- we get values for all iterations.
    P.combine bs ts fs Zero

  where
    -- Compile the boolean vector of conditions for all iterations.
    bs = topFlatten ctx ce
  
    -- For the THEN branch, consider only those iterations in which
    -- the condition is TRUE.
    ts = P.let_ (fst ctx) (P.restrict (envVar ctx) bs Zero)
                          (topFlatten ctx te)

    -- For the ELSE branch, consider only those iterations in which
    -- the condition is FALSE.
    fs = P.let_ (fst ctx) (P.restrict (envVar ctx) (notL bs) Zero)
                          (topFlatten ctx ee)

    notL xs = P.un boolT (SUBoolOp Not) xs (Succ Zero) 

topFlatten ctx (N.AppE1 _ p e)      = prim1 p (topFlatten ctx e) (Succ Zero)
topFlatten ctx (N.AppE2 _ p e1 e2)  = prim2 p (topFlatten ctx e1) (topFlatten ctx e2) (Succ Zero)
topFlatten ctx (N.Comp _ h x xs)    = 
    (P.let_ x currentGen
              (P.let_ (fst ctx) (P.distL (envVar ctx) xv)
                                (runFlat env (deepFlatten h))))

  where
    -- | Initialize the environment for descending into the comprehension head
    env = initEnv x (typeOf currentGen) ctx

    -- | The variable bound by the comprehension, which now refers to
    -- all elements of the source at once.
    xv :: F.LExpr
    xv = F.Var (typeOf currentGen) x

    -- | The compiled generator expression of the current
    -- comprehension, compiled in the context of the topmost
    -- comprehension.
    currentGen :: F.LExpr
    currentGen = topFlatten ctx xs

--------------------------------------------------------------------------------
-- Compile expressions which are nested deeper, i.e. at least at
-- iteration depth 2.

-- | The environment stores all information for dealing with deeper
-- nested expressions.
-- FIXME env should be NonEmpty
data NestedEnv = NestedEnv

    { -- | A reference to the generator expression in the current
      -- iteration context.
      context    :: (Ident, Type)   

      -- | All bindings which are currently in scope and need to be
      -- lifted to the current iteration context.
    , inScope    :: [(Ident, Type)] 

      -- | The current iteration depth
    , frameDepth :: Nat
    }

-- | 'initEnv x xst ctx' constructs the initial environment when a
-- comprehension is encountered at depth 1. 'x' is the variable bound
-- by the inner comprehension, 'xst' is the type of the /translated/
-- generator source expression and 'ctx' is the outer (so far)
-- context.
initEnv :: Ident -> Type -> (Ident, Type) -> NestedEnv
initEnv x xst ctx = 
    NestedEnv { context    = (x, xst)
              , inScope    = map (\(n, t) -> (n, liftType t)) [ctx, (x, xst)]
              , frameDepth = Succ $ Succ Zero
              }


-- | A reader monad that provides access to the flattening
-- environment.
type Flatten a = Reader NestedEnv a

runFlat :: NestedEnv -> Flatten a -> a
runFlat env ma = runReader ma env

-- | Update the environment to express the descent into a
-- comprehension that binds the name 'x'. This involves updating the
-- context, binding 'x' in the current environment frame and
-- increasing the frame depth.
descendEnv :: (Ident, Type) -> NestedEnv -> NestedEnv
descendEnv x env = env { context    = x
                       , inScope    = x : inScope env 
                       , frameDepth = Succ $ frameDepth env
                       }

envVar :: (Ident, Type) -> F.LExpr
envVar (n, t) = F.Var t n

ctxVarM :: Flatten F.LExpr
ctxVarM = envVar <$> asks context

frameDepthM :: Flatten Nat
frameDepthM = asks frameDepth

-- Compile nested expressions that occur with an iteration depth of at
-- least two.
deepFlatten :: N.Expr -> Flatten F.LExpr
deepFlatten (N.Var t v)          = frameDepthM >>= \d -> return $ F.Var (liftTypeN d t) v
deepFlatten (N.Table t n cs hs)  = do
    Succ d1 <- frameDepthM
    ctx     <- ctxVarM
    return $ P.unconcat d1 ctx $ P.dist (F.Table t n cs hs) (P.qconcat d1 ctx)

deepFlatten (N.Const t v)        = do
    Succ d1 <- frameDepthM
    ctx     <- ctxVarM
    return $ P.unconcat d1 ctx $ P.dist (F.Const t v) (P.qconcat d1 ctx)

deepFlatten (N.UnOp t op e1)     = P.un t op <$> deepFlatten e1 <*> frameDepthM
deepFlatten (N.BinOp t op e1 e2) = P.bin t op <$> deepFlatten e1 <*> deepFlatten e2 <*> frameDepthM
deepFlatten (N.AppE1 _ p e)      = prim1 p <$> deepFlatten e <*> frameDepthM
deepFlatten (N.AppE2 _ p e1 e2)  = prim2 p <$> deepFlatten e1 <*> deepFlatten e2 <*> frameDepthM

deepFlatten (N.Let _ x xs e)     = P.let_ x <$> (deepFlatten xs) <*> (deepFlatten e)

deepFlatten (N.If _ ce te ee)    = do
    Succ d1      <- frameDepthM
    
    -- Lift the condition
    bs           <- deepFlatten ce
    
    -- Lift the THEN branch. Note that although the environment record
    -- does not change, all environment variables are re-bound to a
    -- restricted environment by 'restrictEnv'.
    thenExpr     <- deepFlatten te

    -- Lift the ELSE branch. See comment above.
    elseExpr     <- deepFlatten ee

    env          <- asks inScope

    -- Construct the restricted environments in which the THEN and
    -- ELSE branches are evaluated.
    let notL xs = P.un boolT (SUBoolOp Not) xs (Succ d1) 
    
        thenRes = restrictEnv env d1 bs thenExpr

        elseRes = restrictEnv env d1 (notL bs) elseExpr

    return $ P.combine bs thenRes elseRes d1

deepFlatten (N.Comp _ h x xs)    = do
    d@(Succ d1) <- frameDepthM
    env         <- asks inScope
    let cv' = (x, liftTypeN (Succ d) (typeOf xs))
    headExpr    <- local (descendEnv cv') $ deepFlatten h

    xs'         <- deepFlatten xs

    return $ P.let_ x xs' (liftEnv cv' d1 headExpr env)

restrictEnv :: [(Ident, Type)] -> Nat -> F.LExpr -> F.LExpr -> F.LExpr
restrictEnv env d1 bs branchExpr = mkRestrictLet env
  where
    mkRestrictLet :: [(Ident, Type)] -> F.LExpr
    mkRestrictLet (e : []) =
        P.let_ (fst e)
               (P.restrict (envVar e) bs d1)
               branchExpr
    mkRestrictLet (e : es) = 
        P.let_ (fst e)
               (P.restrict (envVar e) bs d1)
               (mkRestrictLet es)

liftEnv :: (Ident, Type) -> Nat -> F.LExpr -> [(Ident, Type)] -> F.LExpr
liftEnv ctx d1 headExpr env = mkLiftingLet env

  where
    mkLiftingLet :: [(Ident, Type)] -> F.LExpr
    mkLiftingLet (e : [])  =
        P.let_ (fst e) 
               (P.unconcat d1 cv (P.distL (P.qconcat d1 $ envVar e) (P.qconcat d1 cv)))
               headExpr
    mkLiftingLet (e : es) =
        P.let_ (fst e) 
               (P.unconcat d1 cv (P.distL (P.qconcat d1 $ envVar e) (P.qconcat d1 cv)))
               (mkLiftingLet es)

    cv :: F.LExpr
    cv = envVar ctx

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

normalize :: F.LExpr -> F.FExpr
normalize e = evalState (normLifting e) 0

-- | Reduce all higher-lifted occurences of primitive combinators and
-- operators to singly lifted variants by flattening the arguments and
-- restoring the original list shape on the result.
normLifting :: F.LExpr -> NormFlat F.FExpr
normLifting (F.Table t n cs hs)    = return $ F.Table t n cs hs
normLifting (F.If t ce te ee)      = F.If t <$> normLifting ce <*> normLifting te <*> normLifting ee
normLifting (F.Const t v)          = return $ F.Const t v
normLifting (F.Var t n)            = return $ F.Var t n
normLifting (F.QConcat n t e)      = F.QConcat n t <$> normLifting e
normLifting (F.UnConcat n t e1 e2) = F.UnConcat n t <$> normLifting e1 <*> normLifting e2
normLifting (F.Let t x e1 e2)      = F.Let t x <$> normLifting e1 <*> normLifting e2
normLifting (F.UnOp t lop e)       = 
    case lop of
        F.LiftedN Zero op          -> F.UnOp t (F.NotLifted op) <$> normLifting e
        F.LiftedN (Succ Zero) op -> F.UnOp t (F.Lifted op) <$> normLifting e
        F.LiftedN (Succ d) op      -> do
            e' <- normLifting e
            n  <- freshNameN
            let v   = F.Var (typeOf e') n
                app = F.UnOp t (F.Lifted op) (P.qconcat d v)
            return $ P.let_ n e' $ P.unconcat d v app

normLifting (F.BinOp t lop e1 e2)  = 
    case lop of
        F.LiftedN Zero op          -> F.BinOp t (F.NotLifted op) 
                                                  <$> normLifting e1
                                                  <*> normLifting e2
        F.LiftedN (Succ Zero) op -> F.BinOp t (F.Lifted op) 
                                                  <$> normLifting e1
                                                  <*> normLifting e2
        F.LiftedN (Succ d) op      -> do
            e1' <- normLifting e1
            e2' <- normLifting e2
            n   <- freshNameN
            let v   = F.Var (typeOf e1') n
                app = F.BinOp t (F.Lifted op) (P.qconcat d v) (P.qconcat d e2')
            return $ P.let_ n e1' $ P.unconcat d v app

normLifting (F.PApp1 t lp e)    = 
    case lp of
        F.LiftedN Zero p          -> F.PApp1 t (F.NotLifted p) <$> normLifting e
        F.LiftedN (Succ Zero) p -> F.PApp1 t (F.Lifted p) <$> normLifting e
        F.LiftedN (Succ d) p      -> do
            e' <- normLifting e
            n  <- freshNameN
            let v   = F.Var (typeOf e') n
                app = F.PApp1 t (F.Lifted p) (P.qconcat d v)
            return $ P.let_ n e' (P.unconcat d v app)

normLifting (F.PApp2 t lp e1 e2)   = 
    case lp of
        F.LiftedN Zero p          -> F.PApp2 t (F.NotLifted p) 
                                                 <$> normLifting e1
                                                 <*> normLifting e2
        F.LiftedN (Succ Zero) p -> F.PApp2 t (F.Lifted p) 
                                                 <$> normLifting e1
                                                 <*> normLifting e2
        F.LiftedN (Succ d) p      -> do
            e1' <- normLifting e1
            e2' <- normLifting e2
            n   <- freshNameN
            let v   = F.Var (typeOf e1') n
                app = F.PApp2 t (F.Lifted p) (P.qconcat d v) (P.qconcat d e2')
            return $ P.let_ n e1' $ P.unconcat d v app

normLifting (F.PApp3 t lp e1 e2 e3)    = 
    case lp of
        F.LiftedN Zero p          -> F.PApp3 t (F.NotLifted p) 
                                                 <$> normLifting e1
                                                 <*> normLifting e2
                                                 <*> normLifting e3
        F.LiftedN (Succ Zero) p -> F.PApp3 t (F.Lifted p) 
                                                 <$> normLifting e1
                                                 <*> normLifting e2
                                                 <*> normLifting e3
        F.LiftedN (Succ d) p      -> do
            e1' <- normLifting e1
            e2' <- normLifting e2
            e3' <- normLifting e3
            n   <- freshNameN
            let v   = F.Var (typeOf e1') n
                app = F.PApp3 t (F.Lifted p) (P.qconcat d v) 
                                             (P.qconcat d e2') 
                                             (P.qconcat d e3')
            return $ P.let_ n e1' $ P.unconcat d v app

