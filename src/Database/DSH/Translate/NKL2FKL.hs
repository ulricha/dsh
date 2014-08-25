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
        
liftPrim1 :: N.Prim1 Type -> F.Expr -> F.Expr
liftPrim1 (N.Prim1 p _) =
    case p of
        N.Length    -> P.lengthL
        N.Concat    -> P.concatL
        N.Sum       -> P.sumL
        N.Avg       -> P.avgL
        N.The       -> P.theL
        N.Fst       -> P.fstL
        N.Snd       -> P.sndL
        N.Head      -> P.headL
        N.Tail      -> P.tailL
        N.Minimum   -> P.minimumL
        N.Maximum   -> P.maximumL
        N.Reverse   -> P.reverseL
        N.And       -> P.andL
        N.Or        -> P.orL
        N.Init      -> P.initL
        N.Last      -> P.lastL
        N.Nub       -> P.nubL
        N.Number    -> P.numberL
        N.Reshape n -> P.reshapeL n
        N.Transpose -> P.transposeL

liftPrim2 :: N.Prim2 Type -> F.Expr -> F.Expr -> F.Expr
liftPrim2 (N.Prim2 p _) =
    case p of
        N.Group        -> P.groupL
        N.Sort         -> P.sortL
        N.Restrict     -> P.restrictL
        N.Pair         -> P.pairL
        N.Append       -> P.appendL
        N.Index        -> P.indexL
        N.Zip          -> P.zipL
        N.Cons         -> P.consL
        N.CartProduct  -> P.cartProductL
        N.NestProduct  -> P.nestProductL
        N.ThetaJoin jp -> P.thetaJoinL jp
        N.NestJoin jp  -> P.nestJoinL jp
        N.SemiJoin jp  -> P.semiJoinL jp
        N.AntiJoin jp  -> P.antiJoinL jp
        

pushComp :: Ident -> F.Expr -> F.Expr -> F.Expr
pushComp = $unimplemented

