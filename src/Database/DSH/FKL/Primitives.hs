{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE TemplateHaskell #-}

-- | Smart constructors for FKL functions and operators
module Database.DSH.FKL.Primitives where

import           Prelude                        hiding (concat, fst, snd)

import           Text.Printf

import           Data.Foldable

import           Database.DSH.Common.Impossible
import           Database.DSH.Common.Lang
import           Database.DSH.Common.Nat
import           Database.DSH.Common.Pretty
import           Database.DSH.Common.Type
import           Database.DSH.FKL.Lang

--------------------------------------------------------------------------------
-- Smart constructors for primitive combinators in the lifting FKL dialect

group :: LExpr -> Nat -> LExpr
group xs d =
    let ListT (TupleT [xt, gt]) = unliftTypeN d $ typeOf xs
        rt                      = ListT (PPairT gt (ListT xt))
    in PApp1 (liftTypeN d rt) Group (LiftedN d) xs

sort :: LExpr -> Nat -> LExpr
sort xs d =
    let ListT (TupleT [xt, _]) = unliftTypeN d $ typeOf xs
    in PApp1 (liftTypeN d (ListT xt)) Sort (LiftedN d) xs

sng :: LExpr -> Nat -> LExpr
sng e d =
    let t = unliftTypeN d $ typeOf e
    in PApp1 (liftTypeN d t) Singleton (LiftedN d) e

only :: LExpr -> Nat -> LExpr
only e1 d =
    let ListT t1 = unliftTypeN d $ typeOf e1
    in PApp1 (liftTypeN d t1) Only (LiftedN d) e1

tuple :: [LExpr] -> Nat -> LExpr
tuple es d =
    let ts = map (unliftTypeN d . typeOf) es
        rt = TupleT ts
    in MkTuple (liftTypeN d rt) (LiftedN d) es

-- zip :: [a] -> [b] -> [(a, b)]
zip :: LExpr -> LExpr -> Nat -> LExpr
zip xs ys d =
    let ListT xt = unliftTypeN d $ typeOf xs
        ListT yt = unliftTypeN d $ typeOf ys
    in PApp2 (liftTypeN d $ ListT (PPairT xt yt)) Zip (LiftedN d) xs ys

cartProduct :: LExpr -> LExpr -> Nat -> LExpr
cartProduct xs ys d =
    let ListT xt = unliftTypeN d $ typeOf xs
        ListT yt = typeOf ys
    in PApp2 (liftTypeN d $ ListT (PPairT xt yt)) CartProduct (LiftedN d) xs ys

thetaJoin :: JoinPredicate ScalarExpr  -> LExpr -> LExpr -> Nat -> LExpr
thetaJoin p xs ys d =
    let ListT xt = unliftTypeN d $ typeOf xs
        ListT yt = unliftTypeN d $ typeOf ys
    in PApp2 (liftTypeN d $ ListT (PPairT xt yt)) (ThetaJoin p) (LiftedN d) xs ys

nestJoin :: JoinPredicate ScalarExpr -> LExpr -> LExpr -> Nat -> LExpr
nestJoin p xs ys d =
    let ListT xt = unliftTypeN d $ typeOf xs
        ListT yt = unliftTypeN d $ typeOf ys
        rt       = ListT (PPairT xt (ListT (PPairT xt yt)))
    in PApp2 (liftTypeN d rt) (NestJoin p) (LiftedN d) xs ys

groupJoin :: JoinPredicate ScalarExpr -> NE AggrApp -> LExpr -> LExpr -> Nat -> LExpr
groupJoin p (NE as) xs ys d =
    let ListT xt = unliftTypeN d $ typeOf xs
        rt       = ListT (TupleT $ xt : toList (fmap aggType as))
    in PApp2 (liftTypeN d rt) (GroupJoin p (NE as)) (LiftedN d) xs ys

semiJoin :: JoinPredicate ScalarExpr -> LExpr -> LExpr -> Nat -> LExpr
semiJoin p e1 e2 d =
    let t1 = unliftTypeN d $ typeOf e1
    in PApp2 (liftTypeN d t1) (SemiJoin p) (LiftedN d) e1 e2

antiJoin :: JoinPredicate ScalarExpr  -> LExpr -> LExpr -> Nat -> LExpr
antiJoin p e1 e2 d =
    let t1 = unliftTypeN d $ typeOf e1
    in PApp2 (liftTypeN d t1) (AntiJoin p) (LiftedN d) e1 e2

append :: LExpr -> LExpr -> Nat -> LExpr
append e1 e2 d =
    let t1 = unliftTypeN d $ typeOf e1
    in PApp2 (liftTypeN d t1) Append (LiftedN d) e1 e2

length :: LExpr -> Nat -> LExpr
length e1 d = PApp1 (liftTypeN d PIntT) (Agg Length) (LiftedN d) e1

nub :: LExpr -> Nat -> LExpr
nub e1 d =
    let t1@(ListT _) = unliftTypeN d $ typeOf e1
    in PApp1 (liftTypeN d t1) Nub (LiftedN d) e1

number :: LExpr -> Nat -> LExpr
number e1 d =
    let ListT t = unliftTypeN d $ typeOf e1
        rt      = (ListT (PPairT t PIntT ))
    in PApp1 (liftTypeN d rt) Number (LiftedN d) e1

reverse :: LExpr -> Nat -> LExpr
reverse e1 d =
    let t1@(ListT _) = unliftTypeN d $ typeOf e1
    in PApp1 (liftTypeN d t1) Reverse (LiftedN d) e1

and :: LExpr -> Nat -> LExpr
and e1 d = PApp1 (liftTypeN d PBoolT) (Agg And) (LiftedN d) e1

or :: LExpr -> Nat -> LExpr
or e1 d = PApp1 (liftTypeN d PBoolT) (Agg Or) (LiftedN d) e1

sum :: LExpr -> Nat -> LExpr
sum e1 d =
    let ListT t = unliftTypeN d $ typeOf e1
    in PApp1 (liftTypeN d t) (Agg Sum) (LiftedN d) e1

avg :: LExpr -> Nat -> LExpr
avg e1 d = case unliftTypeN d $ typeOf e1 of
               ListT PDoubleT  -> PApp1 (liftTypeN d PDoubleT) (Agg Avg) (LiftedN d) e1
               ListT PDecimalT -> PApp1 (liftTypeN d PDecimalT) (Agg Avg) (LiftedN d) e1
               _              -> $impossible

minimum :: LExpr -> Nat -> LExpr
minimum e1 d =
    let ListT t = unliftTypeN d $ typeOf e1
    in PApp1 (liftTypeN d t) (Agg Minimum) (LiftedN d) e1

maximum :: LExpr -> Nat -> LExpr
maximum e1 d =
    let ListT t = unliftTypeN d $ typeOf e1
    in PApp1 (liftTypeN d t) (Agg Maximum) (LiftedN d) e1

concat :: LExpr -> Nat -> LExpr
concat e d =
    let ListT rt@(ListT _) = unliftTypeN d $ typeOf e
    in PApp1 (liftTypeN d rt) Concat (LiftedN d) e

dist :: LExpr -> LExpr -> Nat -> LExpr
dist e1 e2 d =
    let t1 = typeOf e1
    in PApp2 (ListT t1) Dist (LiftedN d) e1 e2

restrict :: LExpr -> Nat -> LExpr
restrict xs d =
    let ListT (TupleT [xt, PBoolT]) = unliftTypeN d $ typeOf xs
    in PApp1 (liftTypeN d (ListT xt)) Restrict (LiftedN d) xs

-- combine :: [Bool] -> [a] -> [a] -> [a]
combine :: LExpr -> LExpr -> LExpr -> Nat -> LExpr
combine e1 e2 e3 d =
    let xst = unliftTypeN d $ typeOf e2
    in PApp3 (liftTypeN d xst) Combine (LiftedN d) e1 e2 e3

tupElem :: TupleIndex -> LExpr -> Nat -> LExpr
tupElem f e d =
    let t = tupleElemT (unliftTypeN d $ typeOf e) f
    in PApp1 (liftTypeN d t) (TupElem f) (LiftedN d) e

if_ :: Typed e => ExprTempl l e -> ExprTempl l e -> ExprTempl l e -> ExprTempl l e
if_ eb et ee =
    let (PBoolT, tt, te) = (typeOf eb, typeOf et, typeOf ee)
    in if tt == te
       then If tt eb et ee
       else error $ printf "FKL.if: incompatible types: %s %s" (pp tt) (pp te)

let_ :: Typed e => Ident -> ExprTempl l e -> ExprTempl l e -> ExprTempl l e
let_ x e1 e2 = Let (typeOf e2) x e1 e2

--------------------------------------------------------------------------------
-- Smart constructors for binary and unary operators.

-- FIXME typing of binary operators is not correct
bin :: Type -> ScalarBinOp -> LExpr -> LExpr -> Nat -> LExpr
bin t o e1 e2 d = BinOp (liftTypeN d t) o (LiftedN d) e1 e2

un :: Type -> ScalarUnOp -> LExpr -> Nat -> LExpr
un t o e d = UnOp (liftTypeN d t) o (LiftedN d) e


--------------------------------------------------------------------------------
-- Smart constructors for special forms in the flat FKL dialect

forget :: Nat -> FExpr -> FExpr
forget n xs =
    let xst = typeOf xs
    in Ext $ Forget n (unwrapListType n xst) xs

unwrapListType :: Nat -> Type -> Type
unwrapListType Zero t               = t
unwrapListType (Succ n') (ListT xt) = unwrapListType n' xt
unwrapListType _         _          = $impossible

imprint :: Nat -> FExpr -> FExpr -> FExpr
imprint n shape bottom = Ext $ Imprint n (wrapListType n bt) shape bottom
  where
    bt = typeOf bottom

wrapListType :: Nat -> Type -> Type
wrapListType Zero t     = t
wrapListType (Succ n') t = wrapListType n' (ListT t)

-- | A regular single 'dist' in the normalized FKL dialect
fdist :: FExpr -> FExpr -> FExpr
fdist e1 e2 = PApp2 (ListT $ typeOf e1) Dist NotLifted e1 e2

--------------------------------------------------------------------------------
-- Smart constructors for special forms in the flat FKL dialect

broadcast :: LExpr -> LExpr -> Nat -> LExpr
broadcast e1 e2 d = Ext $ Broadcast d ty e1 e2
  where
    ty = wrapListType d (typeOf e1)
