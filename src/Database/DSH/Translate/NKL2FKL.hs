{-# LANGUAGE TemplateHaskell #-}
-- | The Flattening Transformation
module Database.DSH.Translate.NKL2FKL (flatTransform) where

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
import           Database.DSH.Impossible
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
-- The flattening transformation

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

-- | Transform a nested expression. This is mostly an identity
-- transformation with one crucial exception: comprehension iterators
-- are eliminated by distributing them over their head expression,
-- i.e. pushing them down.
-- depth = 0
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

-- | Only the iteration context, i.e. the topmost source expression
-- FIXME env should be NonEmpty
data NestedEnv = NestedEnv
    { context    :: (Ident, Type)
    , inScope    :: [(Ident, Type)]
    , frameDepth :: Nat
    }

type Flatten a = ReaderT NestedEnv (State Int) a

runFlat :: NestedEnv -> Flatten a -> a
runFlat env ma = evalState (runReaderT ma env) 1

-- FIXME this should work for now, but is a bit hackish. Implement a
-- clean solution to avoid name collisions.
freshName :: Flatten Ident
freshName = do
    i <- get
    put $ i + 1
    return $ "s" ++ show i

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

-- depth = 1
topFlatten :: (Ident, Type) -> N.Expr -> F.LExpr
topFlatten ctx (N.Table t n cs hs)  = P.dist (F.Table t n cs hs) (envVar ctx)
topFlatten ctx (N.UnOp t op e1)     = P.un t op (topFlatten ctx e1) (Succ Zero)
topFlatten ctx (N.BinOp t op e1 e2) = P.bin t op (topFlatten ctx e1) (topFlatten ctx e2) (Succ Zero)
topFlatten ctx (N.Const t v)        = P.dist (F.Const t v) (envVar ctx)
topFlatten _   (N.Var t v)          = F.Var (liftType t) v
topFlatten ctx (N.If t ce te ee)    = $unimplemented
topFlatten ctx (N.AppE1 _ p e)      = prim1 p (topFlatten ctx e) (Succ Zero)
topFlatten ctx (N.AppE2 _ p e1 e2)  = prim2 p (topFlatten ctx e1) (topFlatten ctx e2) (Succ Zero)
topFlatten ctx (N.Comp t h x xs)    = 
    (P.let_ x (topFlatten ctx xs)
              (P.let_ (fst ctx) (P.distL (envVar ctx) xv)
                                (runFlat env (deepFlatten h))))

  where
    env :: NestedEnv
    env = NestedEnv { context    = (x, listT $ typeOf xs)
                    , inScope    = map (\(n, t) -> (n, liftType t)) [ctx, (x, typeOf xs)]
                    , frameDepth = Succ $ Succ Zero
                    }

    xv :: F.LExpr
    xv = F.Var (liftType $ typeOf xs) x

-- depth >= 2
deepFlatten :: N.Expr -> Flatten F.LExpr
deepFlatten (N.Var t v)          = return $ F.Var (liftType t) v
deepFlatten (N.Table t n cs hs)  = P.dist (F.Table t n cs hs) <$> ctxVarM
deepFlatten (N.Const t v)        = P.dist (F.Const t v) <$> ctxVarM

deepFlatten (N.UnOp t op e1)     = P.un t op <$> deepFlatten e1 <*> frameDepthM
deepFlatten (N.BinOp t op e1 e2) = P.bin t op <$> deepFlatten e1 <*> deepFlatten e2 <*> frameDepthM
deepFlatten (N.AppE1 _ p e)      = prim1 p <$> deepFlatten e <*> frameDepthM
deepFlatten (N.AppE2 _ p e1 e2)  = prim2 p <$> deepFlatten e1 <*> deepFlatten e2 <*> frameDepthM

deepFlatten (N.If t ce te ee)    = $unimplemented

deepFlatten (N.Comp _ h x xs)    = do
    d@(Succ d1) <- frameDepthM
    cv          <- ctxVarM
    env         <- asks inScope
    let cv' = (x, liftTypeN (Succ d) (typeOf xs))
    headExpr    <- local (descendEnv cv') $ deepFlatten h

    xs'         <- deepFlatten xs

    return $ P.let_ x xs' (liftEnv cv' d1 headExpr env)

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
-- Elimination of comprehensions

-- | Push a comprehension through all FKL constructs by lifting
-- primitive functions and distributing over the generator source.
{-
pushComp :: Ident -> F.LExpr -> F.LExpr -> F.LExpr
pushComp _ xs tab@(F.LTable _ _ _ _)  = P.dist tab xs

pushComp _ xs v@(F.LConst _ _)        = P.dist v xs

pushComp x xs y@(F.LVar _ n)
    | x == n                          = xs
    | otherwise                       = P.dist y xs

pushComp x xs (F.LPApp1 t p e1)       = liftPrim1 t p (pushComp x xs e1)

pushComp x xs (F.LPApp2 t p e1 e2)    = 
    liftPrim2 t p (pushComp x xs e1) (pushComp x xs e2)

pushComp x xs (F.LPApp3 t p e1 e2 e3) = 
    liftPrim3 t p (pushComp x xs e1) (pushComp x xs e2) (pushComp x xs e3)

pushComp x xs (F.LBinOp t op e1 e2)   = 
    liftBinOp t op (pushComp x xs e1) (pushComp x xs e2)

pushComp x xs (F.LUnOp t op e)        = 
    liftUnOp t op (pushComp x xs e)

pushComp x xs (F.LIf _ ce te ee)      = 
    P.combine condVec thenVec elseVec
  where
    condVec    = pushComp x xs ce
    thenVec    = pushComp x (P.restrict xs condVec ) te
    negCondVec = F.LUnOp (listT boolT) 
                         (F.LiftedN (Succ Zero) (SUBoolOp Not)) 
                         condVec
    elseVec    = pushComp x (P.restrict xs negCondVec ) ee

-}

--------------------------------------------------------------------------------
-- Normalization of intermediate flat expressions into the final form

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

