{-# LANGUAGE TemplateHaskell #-}

-- | Smart constructors for FKL functions and operators
module Database.DSH.FKL.Primitives where

import Prelude hiding (fst, snd, concat)
       
import Text.Printf

import Database.DSH.Impossible
import Database.DSH.FKL.Lang       as F
import Database.DSH.Common.Pretty
import Database.DSH.Common.Lang
import Database.DSH.Common.Type

--------------------------------------------------------------------------------
-- Smart constructors for primitive combinators in the lifting FKL dialect

-- tranpose :: [[a]] -> [[a]]
transpose :: LExpr -> LExpr
transpose e = 
    let t = typeOf e 
    in F.LPApp1 t (LiftedN Zero F.Transpose) e

-- transpose :: [a] -> [[a]]
reshape :: Integer -> LExpr -> LExpr
reshape n e = 
    let t = typeOf e
    in F.LPApp1 (ListT t) (LiftedN Zero $ F.Reshape n) e

-- group :: [a] -> [b] -> [(a, [b])]
group :: LExpr -> LExpr -> LExpr
group gs xs =
    let ListT xt = typeOf xs
        ListT gt = typeOf gs
        rt             = listT (pairT gt (listT xt))
    in F.LPApp2 rt (LiftedN Zero F.Group) gs xs

-- sort :: [a] -> [b] -> [b]
sort :: LExpr -> LExpr -> LExpr
sort ss xs =
    let xst = typeOf xs
    in F.LPApp2 xst (LiftedN Zero F.Sort) ss xs

cons :: LExpr -> LExpr -> LExpr
cons e1 e2 = 
    let t2 = typeOf e2
    in F.LPApp2 t2 (LiftedN Zero F.Cons) e1 e2

pair :: LExpr -> LExpr -> LExpr
pair e1 e2 = 
    let t1 = typeOf e1
        t2 = typeOf e2
        rt = pairT t1 t2
    in F.LPApp2 rt (LiftedN Zero F.Pair) e1 e2

-- zip :: [a] -> [b] -> [(a, b)]
zip :: LExpr -> LExpr -> LExpr
zip xs ys = 
    let ListT xt = typeOf xs
        ListT yt = typeOf ys
    in F.LPApp2 (listT (pairT xt yt)) (LiftedN Zero F.Zip) xs ys

cartProduct :: LExpr -> LExpr -> LExpr
cartProduct xs ys = 
    let ListT xt = typeOf xs
        ListT yt = typeOf ys
    in F.LPApp2 (listT (pairT xt yt)) (LiftedN Zero F.CartProduct) xs ys
                         
-- nestProduct :: [a] -> [b] -> [(a, [(a, b)])]
nestProduct :: LExpr -> LExpr -> LExpr
nestProduct xs ys = 
    let ListT xt = typeOf xs
        ListT yt = typeOf ys
        rt       = listT (pairT xt (listT (pairT xt yt)))
    in F.LPApp2 rt (LiftedN Zero F.NestProduct) xs ys
                         
thetaJoin :: JoinPredicate JoinExpr  -> LExpr -> LExpr -> LExpr
thetaJoin p xs ys = 
    let ListT xt = typeOf xs
        ListT yt = typeOf ys
    in F.LPApp2 (listT (pairT xt yt)) (LiftedN Zero $ F.ThetaJoin p) xs ys
                         
nestJoin :: JoinPredicate JoinExpr  -> LExpr -> LExpr -> LExpr
nestJoin p xs ys = 
    let ListT xt = typeOf xs
        ListT yt = typeOf ys
        rt       = listT (pairT xt (listT (pairT xt yt)))
    in F.LPApp2 rt (LiftedN Zero $ F.NestJoin p) xs ys
                         
semiJoin :: JoinPredicate JoinExpr  -> LExpr -> LExpr -> LExpr
semiJoin p e1 e2 = 
    let t1 = typeOf e1
    in F.LPApp2 t1 (LiftedN Zero $ F.SemiJoin p) e1 e2
                         
antiJoin :: JoinPredicate JoinExpr  -> LExpr -> LExpr -> LExpr
antiJoin p e1 e2 = 
    let t1 = typeOf e1
    in F.LPApp2 t1 (LiftedN Zero $ F.AntiJoin p) e1 e2
                         
append :: LExpr -> LExpr -> LExpr
append e1 e2 = 
    let t1 = typeOf e1
    in F.LPApp2 t1 (LiftedN Zero F.Append) e1 e2

index :: LExpr -> LExpr -> LExpr
index e1 e2 = 
    let ListT t = typeOf e1
    in F.LPApp2 t (LiftedN Zero F.Index) e1 e2

length :: LExpr -> LExpr
length e1 = F.LPApp1 intT (LiftedN Zero F.Length) e1

-- FIXME this is not the right place to perform this step. If at all,
-- do it during compilation to VL.
head :: LExpr -> LExpr
head = the

the :: LExpr -> LExpr
the e1 = 
    let ListT t1 = typeOf e1
    in F.LPApp1 t1 (LiftedN Zero F.The) e1

last :: LExpr -> LExpr
last e1 = 
    let ListT t1 = typeOf e1
    in F.LPApp1 t1 (LiftedN Zero F.Last) e1

tail :: LExpr -> LExpr
tail e1 = 
    let t1@(ListT _) = typeOf e1
    in F.LPApp1 t1 (LiftedN Zero F.Tail) e1

nub :: LExpr -> LExpr
nub e1 = 
    let t1@(ListT _) = typeOf e1
    in F.LPApp1 t1 (LiftedN Zero F.Nub) e1

number :: LExpr -> LExpr
number e1 = 
    let ListT t = typeOf e1
        rt      = (ListT (PairT t IntT ))
    in F.LPApp1 rt (LiftedN Zero F.Number) e1

init :: LExpr -> LExpr
init e1 = 
    let t1@(ListT _) = typeOf e1
    in F.LPApp1 t1 (LiftedN Zero F.Init) e1

reverse :: LExpr -> LExpr
reverse e1 = 
    let t1@(ListT _) = typeOf e1
    in F.LPApp1 t1 (LiftedN Zero F.Reverse) e1

and :: LExpr -> LExpr
and e1 = F.LPApp1 BoolT (LiftedN Zero F.And) e1

or :: LExpr -> LExpr
or e1 = F.LPApp1 BoolT (LiftedN Zero F.Or) e1

sum :: LExpr -> LExpr
sum e1 = 
    let ListT t = typeOf e1
    in F.LPApp1 t (LiftedN Zero F.Sum) e1
              
avg :: LExpr -> LExpr
avg e1 = F.LPApp1 DoubleT (LiftedN Zero F.Avg) e1

minimum :: LExpr -> LExpr
minimum e1 = 
    let ListT t = typeOf e1
    in F.LPApp1 t (LiftedN Zero F.Minimum) e1

maximum :: LExpr -> LExpr
maximum e1 = 
    let ListT t = typeOf e1
    in F.LPApp1 t (LiftedN Zero F.Maximum) e1

concat :: LExpr -> LExpr
concat e = 
    let ListT rt@(ListT _) = typeOf e
    in F.LPApp1 rt (LiftedN Zero F.Concat) e
                
dist :: LExpr -> LExpr -> LExpr
dist e1 e2 = 
    let t1 = typeOf e1
    in F.LPApp2 (listT t1) (LiftedN Zero F.Dist) e1 e2

restrict :: LExpr -> LExpr -> LExpr
restrict xs bs = 
    let xst = typeOf xs
    in F.LPApp2 xst (LiftedN Zero F.Restrict) xs bs

-- combine :: [Bool] -> [a] -> [a] -> [a]
combine :: LExpr -> LExpr -> LExpr -> LExpr
combine e1 e2 e3 = 
    let xst = typeOf e2
    in F.LPApp3 xst (LiftedN Zero F.Combine) e1 e2 e3

fst :: LExpr -> LExpr
fst e = 
    let PairT t1 _ = typeOf e
    in LPApp1 t1 (LiftedN Zero F.Fst) e

snd :: LExpr -> LExpr
snd e = 
    let PairT _ t2 = typeOf e
    in LPApp1 t2 (LiftedN Zero F.Snd) e

if_ :: LExpr -> LExpr -> LExpr -> LExpr
if_ eb et ee = 
    let (BoolT, tt, te) = (typeOf eb, typeOf et, typeOf ee)
    in if tt == te
       then LIf tt eb et ee
       else error $ printf "FKL.if: incompatible types: %s %s" (pp tt) (pp te)

--------------------------------------------------------------------------------
-- Smart constructors for binary and unary operators.
    
bin :: Type -> ScalarBinOp -> LExpr -> LExpr -> LExpr     
bin t o e1 e2 = 
    case (typeOf e1, o) of
        -- FIXME implementation of equality on tuples should be
        -- performed in the frontend.
        (PairT _ _, SBRelOp Eq) -> 
            bin t (SBBoolOp Conj) (bin t (SBRelOp Eq) (fst e1) (fst e2)) 
                                  (bin t (SBRelOp Eq) (snd e1) (snd e2))
        _                       -> LBinOp t (LiftedN Zero o) e1 e2

un :: Type -> ScalarUnOp -> LExpr -> LExpr
un t o e = LUnOp t (LiftedN Zero o) e

   
--------------------------------------------------------------------------------
-- Smart constructors for primitive combinators in the final FKL dialect

qConcat :: Nat -> Expr -> Expr
qConcat n xs = 
    let xst = typeOf xs
    in QConcat n (unwrapListType n xst) xs

  where
    unwrapListType :: Nat -> Type -> Type
    unwrapListType Zero t               = t
    unwrapListType (Succ n') (ListT xt) = unwrapListType n' xt
    unwrapListType _         _          = $impossible

unconcat :: Nat -> Expr -> Expr -> Expr
unconcat n shape bottom = UnConcat n (wrapListType n bt) shape bottom
  where
    bt = typeOf bottom

    wrapListType :: Nat -> Type -> Type
    wrapListType Zero t     = t
    wrapListType (Succ n') t = wrapListType n' (listT t)

let_ :: Ident -> Expr -> Expr -> Expr
let_ x e1 e = Let (typeOf e) x e1 e
