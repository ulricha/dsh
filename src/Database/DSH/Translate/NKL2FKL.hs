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
flatten (N.UnOp t op e1)     = F.UnOp t (F.NotLifted op) (flatten e1)
flatten (N.BinOp t op e1 e2) = F.BinOp t (F.NotLifted op) (flatten e1) (flatten e2)
flatten (N.Const t v)        = F.Const t v
flatten (N.Var t v)          = F.Var t v
flatten (N.If t ce te ee)    = F.If t (flatten ce) (flatten te) (flatten ee)
flatten (N.AppE1 t p e)      = prim1 p $ flatten e
flatten (N.AppE2 t p e1 e2)  = prim2 p (flatten e1) (flatten e2)
flatten (N.Comp t h x xs)    = pushComp x (flatten xs) (flatten h)

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
        
liftPrim1 :: F.Prim1 -> F.Expr -> F.Expr
liftPrim1 p =
    case p of
        F.Length    -> P.lengthL
        F.Concat    -> P.concatL
        F.Sum       -> P.sumL
        F.Avg       -> P.avgL
        F.The       -> P.theL
        F.Fst       -> P.fstL
        F.Snd       -> P.sndL
        F.Tail      -> P.tailL
        F.Minimum   -> P.minimumL
        F.Maximum   -> P.maximumL
        F.Reverse   -> P.reverseL
        F.And       -> P.andL
        F.Or        -> P.orL
        F.Init      -> P.initL
        F.Last      -> P.lastL
        F.Nub       -> P.nubL
        F.Number    -> P.numberL
        F.Reshape n -> P.reshapeL n
        F.Transpose -> P.transposeL

liftPrim2 :: F.Prim2 -> F.Expr -> F.Expr -> F.Expr
liftPrim2 p =
    case p of
        F.Group        -> P.groupL
        F.Sort         -> P.sortL
        F.Restrict     -> P.restrictL
        F.Pair         -> P.pairL
        F.Append       -> P.appendL
        F.Index        -> P.indexL
        F.Zip          -> P.zipL
        F.Cons         -> P.consL
        F.CartProduct  -> P.cartProductL
        F.NestProduct  -> P.nestProductL
        F.ThetaJoin jp -> P.thetaJoinL jp
        F.NestJoin jp  -> P.nestJoinL jp
        F.SemiJoin jp  -> P.semiJoinL jp
        F.AntiJoin jp  -> P.antiJoinL jp
        

pushComp :: Ident -> F.Expr -> F.Expr -> F.Expr
pushComp x xs v@(F.Const _ _)       = P.concat $ P.dist v xs
pushComp x xs y@(F.Var _ n)
    | x == n                    = xs
    | otherwise                 = P.concat $ P.dist y xs
pushComp x xs (F.PApp1 _ p e1)    = liftPrim1 p (pushComp x xs e1)
pushComp x xs (F.PApp2 _ p e1 e2) = liftPrim2 p (pushComp x xs e1) (pushComp x xs e2)
pushComp x xs (F.UnOp t (F.NotLifted op) e1) = P.unL t op (pushComp x xs e1)
pushComp x xs (F.BinOp t (F.NotLifted op) e1 e2) = P.binL t op (pushComp x xs e1) (pushComp x xs e2)


