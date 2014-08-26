{-# LANGUAGE TemplateHaskell #-}
module Database.DSH.Translate.NKL2FKL (flatten) where

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

flatten :: N.Expr -> F.Expr
flatten (N.Table t n cs hs)  = F.Table t n cs hs
flatten (N.UnOp t op e1)     = P.un t op (flatten e1)
flatten (N.BinOp t op e1 e2) = P.bin t op (flatten e1) (flatten e2)
flatten (N.Const t v)        = F.Const t v
flatten (N.Var t v)          = F.Var t v
flatten (N.If t ce te ee)    = F.If t (flatten ce) (flatten te) (flatten ee)
flatten (N.AppE1 _ p e)      = prim1 p $ flatten e
flatten (N.AppE2 _ p e1 e2)  = prim2 p (flatten e1) (flatten e2)
flatten (N.Comp _ h x xs)    = pushComp x (flatten xs) (flatten h)

prim1 :: N.Prim1 Type -> F.Expr -> F.Expr
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

prim2 :: N.Prim2 Type -> F.Expr -> F.Expr -> F.Expr
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

liftPrim1 :: Type -> F.LiftedN F.Prim1 -> F.Expr -> F.Expr
liftPrim1 t (F.LiftedN n p) = F.PApp1 (liftType t) (F.LiftedN (F.Succ n) p)

liftPrim2 :: Type -> F.LiftedN F.Prim2 -> F.Expr -> F.Expr -> F.Expr
liftPrim2 t (F.LiftedN n p) = F.PApp2 (liftType t) (F.LiftedN (F.Succ n) p)

liftPrim3 :: Type -> F.LiftedN F.Prim3 -> F.Expr -> F.Expr -> F.Expr -> F.Expr
liftPrim3 t (F.LiftedN n p) = F.PApp3 (liftType t) (F.LiftedN (F.Succ n) p)

liftBinOp :: Type -> F.LiftedN ScalarBinOp -> F.Expr -> F.Expr -> F.Expr
liftBinOp t (F.LiftedN n op) = F.BinOp (liftType t) (F.LiftedN (F.Succ n) op)

liftUnOp :: Type -> F.LiftedN ScalarUnOp -> F.Expr -> F.Expr
liftUnOp t (F.LiftedN n op) = F.UnOp (liftType t) (F.LiftedN (F.Succ n) op)


-- | Push a comprehension through all FKL constructs by lifting
-- primitive functions and distributing over the generator source.
pushComp :: Ident -> F.Expr -> F.Expr -> F.Expr
pushComp _ xs tab@(F.Table _ _ _ _) = P.dist tab xs

pushComp _ xs v@(F.Const _ _)       = P.dist v xs

pushComp x xs y@(F.Var _ n)
    | x == n                    = xs
    | otherwise                 = P.dist y xs

pushComp x xs (F.PApp1 t p e1)    = liftPrim1 t p (pushComp x xs e1)

pushComp x xs (F.PApp2 t p e1 e2) = liftPrim2 t p (pushComp x xs e1) (pushComp x xs e2)

pushComp x xs (F.PApp3 t p e1 e2 e3) = liftPrim3 t p (pushComp x xs e1) (pushComp x xs e2) (pushComp x xs e3)

pushComp x xs (F.BinOp t op e1 e2) = liftBinOp t op (pushComp x xs e1) (pushComp x xs e2)

pushComp x xs (F.UnOp t op e)      = liftUnOp t op (pushComp x xs e)

pushComp x xs (F.If _ ce te ee)    = P.combine condVec thenVec elseVec
  where
    condVec = pushComp x xs ce
    thenVec = pushComp x (P.restrict condVec xs) te
    elseVec = pushComp x (P.restrict (F.UnOp (listT boolT) 
                                             (F.LiftedN (F.Succ F.Zero) (SUBoolOp Not)) 
                                             condVec) 
                                     xs) ee

-- | Reduce all higher-lifted occurences of primitive combinators and
-- operators to singly lifted variants.
normLifting :: F.Expr -> F.FExpr
normLifting (F.Table t n cs hs) = F.FTable t n cs hs
normLifting (F.If t ce te ee)   = F.FIf t (normLifting ce) (normLifting te) (normLifting ee)
normLifting (F.Const t v)       = F.FConst t v
normLifting (F.Var _ _)         = $impossible


