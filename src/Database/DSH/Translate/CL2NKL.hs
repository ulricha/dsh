{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TemplateHaskell  #-}
{-# LANGUAGE BangPatterns     #-}

module Database.DSH.Translate.CL2NKL
  ( desugarComprehensions ) where

#ifdef DEBUGCOMP
import           Debug.Trace
import           Database.DSH.Common.Pretty
#endif

import           Data.List.NonEmpty          (NonEmpty(..))
import qualified Data.List.NonEmpty          as N
import qualified Data.Foldable               as F
import           Control.Monad.Reader
import           Control.Applicative

import           Database.DSH.Common.Impossible

import           Database.DSH.Common.Type
import           Database.DSH.Common.Lang

import           Database.DSH.CL.Lang        (toList)
import qualified Database.DSH.CL.Lang        as CL
import qualified Database.DSH.NKL.Primitives as P
import qualified Database.DSH.NKL.Lang       as NKL
import           Database.DSH.NKL.Rewrite

--------------------------------------------------------------------------------
-- Conversion of primitive operators

prim1 :: Type -> CL.Prim1 -> CL.Expr -> NameEnv NKL.Expr
prim1 t p e = mkApp t <$> expr e
  where
    mkApp =
        case p of
            CL.Singleton        -> mkPrim1 NKL.Singleton
            CL.Length           -> mkPrim1 NKL.Length
            CL.Concat           -> mkPrim1 NKL.Concat
            -- Null in explicit form is useful during CL optimization
            -- to easily recognize universal/existential patterns. In
            -- backend implementations however, there currently is no
            -- need to store it explicitly. Therefore, we implement it
            -- using length in NKL.
            CL.Null             -> nklNull
            CL.Sum              -> mkPrim1 NKL.Sum
            CL.Avg              -> mkPrim1 NKL.Avg
            CL.The              -> mkPrim1 NKL.The
            CL.Head             -> mkPrim1 NKL.Head
            CL.Minimum          -> mkPrim1 NKL.Minimum
            CL.Maximum          -> mkPrim1 NKL.Maximum
            CL.Tail             -> mkPrim1 NKL.Tail
            CL.Reverse          -> mkPrim1 NKL.Reverse
            CL.And              -> mkPrim1 NKL.And
            CL.Or               -> mkPrim1 NKL.Or
            CL.Init             -> mkPrim1 NKL.Init
            CL.Last             -> mkPrim1 NKL.Last
            CL.Nub              -> mkPrim1 NKL.Nub
            CL.Number           -> mkPrim1 NKL.Number
            (CL.Reshape n)      -> mkPrim1 $ NKL.Reshape n
            CL.Transpose        -> mkPrim1 NKL.Transpose
            CL.TupElem i        -> mkPrim1 $ NKL.TupElem i
            CL.Sort             -> mkPrim1 NKL.Sort
            CL.Group            -> mkPrim1 NKL.Group
            CL.Guard            -> $impossible

    nklNull _ ne = NKL.BinOp boolT
                             (SBRelOp Eq)
                             (NKL.Const intT $ IntV 0)
                             (NKL.AppE1 intT NKL.Length ne)

    mkPrim1 nop nt ne = NKL.AppE1 nt nop ne


-- | Transform applications of binary primitives.
prim2 :: Type -> CL.Prim2 -> CL.Expr -> CL.Expr -> NameEnv NKL.Expr
prim2 t o e1 e2 = mkApp2
  where
    mkApp2 =
        case o of
            CL.Append       -> mkPrim2 NKL.Append
            CL.Index        -> mkPrim2 NKL.Index
            CL.Zip          -> mkPrim2 NKL.Zip
            CL.CartProduct  -> mkPrim2 NKL.CartProduct
            CL.NestProduct  -> mkPrim2 NKL.NestProduct
            CL.ThetaJoin p  -> mkPrim2 $ NKL.ThetaJoin p
            CL.NestJoin p   -> mkPrim2 $ NKL.NestJoin p
            CL.SemiJoin p   -> mkPrim2 $ NKL.SemiJoin p
            CL.AntiJoin p   -> mkPrim2 $ NKL.AntiJoin p

    mkPrim2 :: NKL.Prim2 -> NameEnv NKL.Expr
    mkPrim2 nop = NKL.AppE2 t nop <$> expr e1 <*> expr e2

--------------------------------------------------------------------------------
-- Generator environments

-- | Access a component of a tuple variable
type TupleAccessor = Type -> Ident -> NKL.Expr

type EnvEntry = (Ident, Type, TupleAccessor)

-- | A generator environment stores generator variables that have
-- already been handled in the traversal of the qualifier list. For
-- each variable, we store it's type and an expression that projects
-- the variables' value out of the constructed tuple.
type GenEnv = N.NonEmpty EnvEntry

-- | Construct an environment from one generator variable
-- => (x, t, \n t -> Var t n)
mkEnv :: (Ident, Type) -> GenEnv
mkEnv (x, xt) = (x, xt, \n t -> NKL.Var n t) N.:| []

-- | Account for a new pair that has been added at the top of the
-- constructed tuple
updateEnvEntry :: EnvEntry -> EnvEntry
updateEnvEntry (x, t, ta) = (x, t, \n t' -> P.fst $ ta n t')

-- | Extend an environment with an additional generator variable.
extendEnv :: GenEnv -> (Ident, NKL.Expr) -> GenEnv
extendEnv entries (y, ys) =  entry N.<| fmap updateEnvEntry entries
  where
    entry = (y, elemT $ typeOf ys, \n t -> P.snd $ NKL.Var n t)

addGensToEnv :: NonEmpty (Ident, NKL.Expr) -> GenEnv -> GenEnv
addGensToEnv gens env = F.foldl' extendEnv env gens

--------------------------------------------------------------------------------
-- Conversion of CL expressions to NKL expressions

type NameEnv a = Reader [Ident] a

freshName :: NameEnv Ident
freshName = do
    boundNames <- ask
    return $ tryName 0 boundNames

  where
    tryName :: Int -> [Ident] -> Ident
    tryName i ns = if mkName i `elem` ns
                   then tryName (i + 1) ns
                   else mkName i

    mkName i = "f" ++ show i

-- | Map a CL expression to its NKL equivalent by desugaring all
-- comprehensions.
expr :: CL.Expr -> NameEnv NKL.Expr
expr (CL.MkTuple t es)           = NKL.MkTuple t <$> mapM expr es
expr (CL.Table t s cs ks)        = return $ NKL.Table t s cs ks
expr (CL.AppE1 t p e)            = prim1 t p e
expr (CL.AppE2 t p e1 e2)        = prim2 t p e1 e2
expr (CL.BinOp t o e1 e2)        = NKL.BinOp t o <$> expr e1 <*> expr e2
expr (CL.UnOp t o e)             = NKL.UnOp t o <$> expr e
expr (CL.If t c th el)           = NKL.If t <$> expr c <*> expr th <*> expr el
expr (CL.Lit t v)                = return $ NKL.Const t v
expr (CL.Var t v)                = return $ NKL.Var t v
expr (CL.Comp t e qs)            = desugarComprehension t e (toList qs)
expr (CL.Let t x e1 e2)          = NKL.Let t x <$> expr e1 <*> local (x :) (expr e2)

--------------------------------------------------------------------------------
-- Desugaring of comprehensions
--
-- We do not use a general desugaring scheme for monad comprehensions
-- but deal only with list comprehensions. The motivation for now is
-- to avoid inefficient patterns (e.g. the handling of guards via
-- 'if') already by construction.
-- 
-- In the current qualifier list, we consider the longest prefix of
-- generators. The cartesian product of those generators is
-- computed. We compute the cartesian product using nested
-- concatMaps. This is necessary because a generator expression might
-- depend on a preceding generator variable. If a guard follows a
-- sequence of generators, it is turned into a filter applied to the
-- cartesian product of all preceding generators.
--
-- Example:
-- 
-- [ e x y z | x <- xs, y <- ys, p1 x y, z <- zs, p2 y z ]
-- =>
-- map (\t -> e [x/fst (fst t)] [y/snd (fst t)] [z/snd t])
--     (filter (\t -> p2[y/snd (fst t)][z/snd t])
--             (concatMap (\t -> concatMap (\z -> [pair t z]) zs[x/fst t][y/snd t])
--                        (filter (\t -> p1[x/fst t][y/snd t])
--                                (concatMap (\t -> concatMap (\y -> pair t y) ys[x/t])
--                                           xs

-- | Split a qualifier list into a prefix of generators and the
-- remaining qualifiers.
takeGens :: [CL.Qual] -> ([(Ident, CL.Expr)], [CL.Qual])
takeGens (CL.BindQ x xs : qs) = let (binds, rest) = takeGens qs in ((x, xs) : binds, rest)
takeGens qs                   = ([], qs)

-- | Generate an identifier that does not occur in the list provided.
freshIdent :: [Ident] -> NameEnv Ident
freshIdent names = do
    visibleNames <- ask
    return $ checkCollision (0 :: Int) (names ++ visibleNames)
  where
    checkCollision i ns = if mkName i `elem` ns
                          then checkCollision (i + 1) ns
                          else mkName i

    mkName i = "v" ++ show i

-- | Construct a left-deep tuple from a list of expressions
mkTuple :: NonEmpty NKL.Expr -> NKL.Expr
mkTuple xs = F.foldl1 P.pair xs

-- | Produce the nested concatMaps from a sequence of generators. The
-- body of the innermost generator constructs the tuple of generator
-- variables.
-- x <- xs, y <- ys, z <- zs
-- =>
-- concatMap (\x -> concatMap (\y -> concatMap (\z -> (((t, x), y), z)) zs) ys) xs
-- where t is the binding variable for the base expression.
nestQualifiers :: NKL.Expr -> [(Ident, NKL.Expr)] -> NKL.Expr
nestQualifiers tupConst ((x, xs) : qs) = P.concat $ NKL.Iterator (listT bodyType) compHead x xs
  where
    compHead  = nestQualifiers tupConst qs
    bodyType = typeOf compHead
nestQualifiers tupConst []             = tupConst

-- | Desugar a sequence of generators.
desugarGens :: GenEnv -> NKL.Expr -> NonEmpty (Ident, NKL.Expr) -> NameEnv NKL.Expr
desugarGens env baseExpr qs = do
    -- Avoid all names that are bound by enclosing binders and the
    -- ones bound in the current generator list.
    visibleNames <- (++) (map fst $ N.toList qs) <$> ask

    -- Avoid all names that are bound in the generator expressions in
    -- which we will substitute.
    let boundNames = concatMap (boundVars . snd) $ N.toList qs
        avoidNames = boundNames ++ visibleNames

    outerName    <- freshIdent $ visibleNames ++ boundNames

    let baseElemType   = elemT $ typeOf baseExpr

        -- Generator expressions might reference variables bound by
        -- preceding generators. These variables go out of scope during
        -- desugaring. To eliminate them, we have to replace references to
        -- generator variables in generator expressions by the appropriate
        -- tuple accessors for the outer concatMap variable.
        substGenExpr (n, e) = (n, substTupleAccesses avoidNames (outerName, baseElemType) env e)

    let qs'            = fmap substGenExpr qs

        tupConst       = P.sng $ mkTuple $ fmap mkVar ((outerName, baseExpr) N.<| qs')
        mkVar (x, xs)  = NKL.Var (elemT $ typeOf xs) x
        gensExpr       = nestQualifiers tupConst (N.toList qs')
        compTy         = (listT $ typeOf tupConst)
    return $ P.concat $ NKL.Iterator compTy gensExpr outerName baseExpr

-- | Replace every occurence of a generator variable with the
-- corresponding tuple access expression.
substTupleAccesses :: [Ident] -> (Ident, Type) -> GenEnv -> NKL.Expr -> NKL.Expr
substTupleAccesses visibleNames (n, t) env e = F.foldr substTupleAccess e env
  where
    substTupleAccess (x, _, xta) e' = subst (n : visibleNames) x (xta t n) e'

qualVar :: CL.Qual -> [Ident]
qualVar (CL.BindQ x _) = [x]
qualVar (CL.GuardQ _)  = []

-- | Transform a list of generator expressions to NKL
-- expressions. Every expression is transformed in the name
-- environment enriched with the current prefix of the generators.
genExprs :: NonEmpty (Ident, CL.Expr) -> NameEnv (NonEmpty (Ident, NKL.Expr))
genExprs ((n, e) :| [])       = do
    e' <- expr e
    return $ (n, e') :| []
genExprs ((n, e) :| (q : qs)) = do
    e'  <- expr e
    qs' <- local (n :) (genExprs $ q :| qs)
    return $ (n, e') N.<| qs'

-- | Desugar a list of qualifiers. The second parameter 'baseSrc' is
-- the (filtered) cartesian product of all generators that have been
-- desugared so far.
desugarQualsRec :: GenEnv -> NKL.Expr -> [CL.Qual] -> NameEnv (GenEnv, NKL.Expr)
-- If we encounter a generator, we produce the cartesian product of
-- the generator prefix of the current qualifier list.
desugarQualsRec env baseSrc (CL.BindQ x xs : qs) = do
    let (gens, remQuals) = takeGens qs
        genNames         = map fst gens
    nklGens  <- genExprs ((x, xs) :| gens)
    baseSrc' <- desugarGens env baseSrc nklGens
    let env' = addGensToEnv nklGens env

    local (++ genNames) $ desugarQualsRec env' baseSrc' remQuals

-- A guard is desugared by filtering the cartesian product of the
-- generators that have been encountered so far.
desugarQualsRec env baseSrc (CL.GuardQ p : qs)    = do
    p'           <- expr p
    visibleNames <- ask

    filterName   <- freshIdent $ visibleNames ++ boundVars p'

    let elemTy        = elemT $ typeOf baseSrc
        filterExpr    = substTupleAccesses visibleNames (filterName, elemTy) env p'

        predTy        = listT (pairT elemTy boolT)
        predPairConst = P.tuple [NKL.Var elemTy filterName, filterExpr]
        -- Construct an iterator that pairs every input element with
        -- the corresponding result of the predicate:
        --
        -- [ (x, p x) | x <- xs ]
        predIter      = NKL.Iterator predTy predPairConst filterName baseSrc
        filterSrc     = P.restrict predIter

    desugarQualsRec env filterSrc qs

desugarQualsRec env baseSrc []                    = return (env, baseSrc)

-- | Kick off the recursive traversal of the qualifier list.
desugarQuals :: [CL.Qual] -> NameEnv (GenEnv, NKL.Expr, NKL.Expr -> NKL.Expr)
desugarQuals []                   = $impossible
-- If the first qualifier is a guard, employ an if with a [] else
-- branch.
desugarQuals (CL.GuardQ p : qs)   = do
    (env, genExpr, _) <- desugarQuals qs
    p'                <- expr p
    let wrapIf iter = P.if_  p' iter (NKL.Const (typeOf iter) (ListV []))
    return (env, genExpr, wrapIf)
-- If the first qualifier is a generator, it becomes the base source
-- expression.
desugarQuals (CL.BindQ x xs : qs) = do
    let xt  = elemT $ typeOf xs
    let env = mkEnv (x, xt)
    xs'             <- expr xs
    (env', genExpr) <- desugarQualsRec env xs' qs
    return (env', genExpr, id)

-- | Desugaring of comprehensions happens in two steps: Desugaring the
-- qualifiers leads to an expression that produces the (properly
-- filtered) cartesian product of all qualifiers. The head expression
-- ist then simply mapped over the resulting list.
desugarComprehension:: Type -> CL.Expr -> [CL.Qual] -> NameEnv NKL.Expr
desugarComprehension _ e qs = do
    -- Desugar the qualifiers
    (env, genExpr, wrapHead) <- desugarQuals qs

    let genNames = concatMap qualVar qs

    e'             <- local (++ genNames) (expr e)
    -- All names that are bound in enclosing scopes, including names
    -- bound by local generators
    visibleNames   <- (++) genNames <$> ask

    -- Avoid all visible names
    n              <- freshIdent $ visibleNames ++ boundVars e'

    let t       = elemT $ typeOf genExpr

        -- In the head expression, turn references to generator
        -- variables into references to the (freshly chosen) map
        -- variable. For substitution in the expression, we avoid all
        -- names that are currently visible, including generator names
        -- that are by now no longer visible. This should not hurt
        -- though, as the information is only used for alpha-conversion
        -- on lambdas during substitution.
        e''      = substTupleAccesses visibleNames (n, t) env e'

    return $ wrapHead $ NKL.Iterator (listT $ typeOf e') e'' n genExpr

-- | Express comprehensions through NKL iteration constructs map and
-- concatMap and filter.
desugarComprehensions :: CL.Expr -> NKL.Expr
desugarComprehensions e =
#ifdef DEBUGCOMP
    trace (debugPrint eo) eo

  where
    eo = runReader (expr e) []

    padSep :: String -> String
    padSep s = "\n" ++ s ++ " " ++ replicate (100 - length s) '=' ++ "\n"

    debugPrint :: NKL.Expr -> String
    debugPrint e' = padSep "Desugared NKL" ++ pp e' ++ padSep ""
#else
    runReader (expr e) []
#endif
