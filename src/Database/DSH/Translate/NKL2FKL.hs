{-# LANGUAGE TemplateHaskell #-}
module Database.DSH.Translate.NKL2FKL (flatTransform) where

#ifdef DEBUGCOMP
import           Debug.Trace
import           Database.DSH.Common.Pretty
#endif

import           Control.Applicative
import           Control.Monad
import           Control.Monad.State         hiding (lift)
import           Data.List

import           Database.DSH.Common.Lang
import           Database.DSH.Common.Type
import qualified Database.DSH.FKL.Lang       as F
import qualified Database.DSH.FKL.Primitives as P
import           Database.DSH.Impossible
import qualified Database.DSH.NKL.Lang       as N
import qualified Database.DSH.NKL.Rewrite    as NR

-- | Transform an expression in the Nested Kernel Language into its
-- equivalent Flat Kernel Language expression by means of the
-- flattening transformation.
flatTransform :: N.Expr -> F.Expr
flatTransform expr = 
#ifdef DEBUGCOMP
    let lexpr = flatten expr
        fexpr = normLifting lexpr
    in trace (decorate "Flattened" lexpr) $
       trace (decorate "Normalized Flat" fexpr) $
       fexpr

  where
    padSep :: String -> String
    padSep s = "\n" ++ s ++ " " ++ replicate (100 - length s) '=' ++ "\n"

    decorate :: Pretty e => String -> e -> String
    decorate msg e = padSep msg ++ pp e ++ padSep ""
    
#else
    normLifting $ flatten expr
#endif

--------------------------------------------------------------------------------
-- The flattening transformation

prim1 :: N.Prim1 Type -> F.LExpr -> F.LExpr
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

prim2 :: N.Prim2 Type -> F.LExpr -> F.LExpr -> F.LExpr
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
flatten :: N.Expr -> F.LExpr
flatten (N.Table t n cs hs)  = F.LTable t n cs hs
flatten (N.UnOp t op e1)     = P.un t op (flatten e1)
flatten (N.BinOp t op e1 e2) = P.bin t op (flatten e1) (flatten e2)
flatten (N.Const t v)        = F.LConst t v
flatten (N.Var t v)          = F.LVar t v
flatten (N.If t ce te ee)    = F.LIf t (flatten ce) (flatten te) (flatten ee)
flatten (N.AppE1 _ p e)      = prim1 p $ flatten e
flatten (N.AppE2 _ p e1 e2)  = prim2 p (flatten e1) (flatten e2)
flatten (N.Comp _ h x xs)    = pushComp x (flatten xs) (flatten h)

--------------------------------------------------------------------------------
-- Elimination of comprehensions

liftPrim1 :: Type -> F.LiftedN F.Prim1 -> F.LExpr -> F.LExpr
liftPrim1 t (F.LiftedN n p) = F.LPApp1 (liftType t) (F.LiftedN (F.Succ n) p)

liftPrim2 :: Type -> F.LiftedN F.Prim2 -> F.LExpr -> F.LExpr -> F.LExpr
liftPrim2 t (F.LiftedN n p) = F.LPApp2 (liftType t) (F.LiftedN (F.Succ n) p)

liftPrim3 :: Type -> F.LiftedN F.Prim3 -> F.LExpr -> F.LExpr -> F.LExpr -> F.LExpr
liftPrim3 t (F.LiftedN n p) = F.LPApp3 (liftType t) (F.LiftedN (F.Succ n) p)

liftBinOp :: Type -> F.LiftedN ScalarBinOp -> F.LExpr -> F.LExpr -> F.LExpr
liftBinOp t (F.LiftedN n op) = F.LBinOp (liftType t) (F.LiftedN (F.Succ n) op)

liftUnOp :: Type -> F.LiftedN ScalarUnOp -> F.LExpr -> F.LExpr
liftUnOp t (F.LiftedN n op) = F.LUnOp (liftType t) (F.LiftedN (F.Succ n) op)


-- | Push a comprehension through all FKL constructs by lifting
-- primitive functions and distributing over the generator source.
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
    thenVec    = pushComp x (P.restrict condVec xs) te
    negCondVec = F.LUnOp (listT boolT) 
                         (F.LiftedN (F.Succ F.Zero) (SUBoolOp Not)) 
                         condVec
    elseVec    = pushComp x (P.restrict negCondVec xs) ee

--------------------------------------------------------------------------------
-- Normalization of intermediate flat expressions into the final form

-- | Reduce all higher-lifted occurences of primitive combinators and
-- operators to singly lifted variants by flattening the arguments and
-- restoring the original list shape on the result.
normLifting :: F.LExpr -> F.Expr
normLifting (F.LTable t n cs hs) = F.Table t n cs hs
normLifting (F.LIf t ce te ee)   = F.If t (normLifting ce) (normLifting te) (normLifting ee)
normLifting (F.LConst t v)       = F.Const t v
normLifting (F.LVar _ _)         = $impossible
normLifting (F.LUnOp t lop e)    = 
    case lop of
        F.LiftedN F.Zero op          -> F.UnOp t (F.NotLifted op) (normLifting e)
        F.LiftedN (F.Succ F.Zero) op -> F.UnOp t (F.Lifted op) (normLifting e)
        F.LiftedN (F.Succ n) op      -> 
            let e'  = normLifting e
                app = F.UnOp t (F.Lifted op) (P.concatN n e')
            in P.unconcat n e' app

normLifting (F.LBinOp t lop e1 e2)    = 
    case lop of
        F.LiftedN F.Zero op          -> F.BinOp t (F.NotLifted op) 
                                                  (normLifting e1) 
                                                  (normLifting e2)
        F.LiftedN (F.Succ F.Zero) op -> F.BinOp t (F.Lifted op) 
                                                  (normLifting e1)
                                                  (normLifting e2)
        F.LiftedN (F.Succ n) op      -> 
            let e1'  = normLifting e1
                e2'  = normLifting e2
                app = F.BinOp t (F.Lifted op) (P.concatN n e1') (P.concatN n e2')
            in P.unconcat n e1' app

normLifting (F.LPApp1 t lp e1)    = 
    case lp of
        F.LiftedN F.Zero p          -> F.PApp1 t (F.NotLifted p) (normLifting e1) 
        F.LiftedN (F.Succ F.Zero) p -> F.PApp1 t (F.Lifted p) (normLifting e1)
        F.LiftedN (F.Succ n) p      -> 
            let e1'  = normLifting e1
                app = F.PApp1 t (F.Lifted p) (P.concatN n e1')
            in P.unconcat n e1' app

normLifting (F.LPApp2 t lp e1 e2)    = 
    case lp of
        F.LiftedN F.Zero p          -> F.PApp2 t (F.NotLifted p) 
                                                 (normLifting e1) 
                                                 (normLifting e2)
        F.LiftedN (F.Succ F.Zero) p -> F.PApp2 t (F.Lifted p) 
                                                 (normLifting e1)
                                                 (normLifting e2)
        F.LiftedN (F.Succ n) p      -> 
            let e1'  = normLifting e1
                e2'  = normLifting e2
                app = F.PApp2 t (F.Lifted p) (P.concatN n e1') (P.concatN n e2')
            in P.unconcat n e1' app

normLifting (F.LPApp3 t lp e1 e2 e3)    = 
    case lp of
        F.LiftedN F.Zero p          -> F.PApp3 t (F.NotLifted p) 
                                                 (normLifting e1) 
                                                 (normLifting e2)
                                                 (normLifting e3)
        F.LiftedN (F.Succ F.Zero) p -> F.PApp3 t (F.Lifted p) 
                                                 (normLifting e1)
                                                 (normLifting e2)
                                                 (normLifting e3)
        F.LiftedN (F.Succ n) p      -> 
            let e1'  = normLifting e1
                e2'  = normLifting e2
                e3'  = normLifting e3
                app = F.PApp3 t (F.Lifted p) 
                                (P.concatN n e1') 
                                (P.concatN n e2') 
                                (P.concatN n e2')
            in P.unconcat n e1' app
