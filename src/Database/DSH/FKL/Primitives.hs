{-# LANGUAGE TemplateHaskell #-}

-- | Smart constructors for FKL functions and operators
module Database.DSH.FKL.Primitives where

import Prelude hiding (fst, snd)
       
import Text.Printf

import Database.DSH.Impossible
import Database.DSH.FKL.Lang       as F
import Database.DSH.Common.Pretty
import Database.DSH.Common.Lang
import Database.DSH.Common.Type

import Control.Monad

--------------------------------------------------------------------------------
-- Smart constructors for primitive combinators

-- tranpose :: [[a]] -> [[a]]
transpose :: Expr -> Expr
transpose e = 
    let t = typeOf e 
    in F.PApp1 t (LiftedN Zero F.Transpose) e

-- transpose :: [a] -> [[a]]
reshape :: Integer -> Expr -> Expr
reshape n e = 
    let t = typeOf e
    in F.PApp1 (ListT t) (LiftedN Zero $ F.Reshape n) e

group :: Expr -> Expr -> Expr
group gs xs =
    let ListT xt = typeOf xs
        ListT gt = typeOf gs
        rt             = listT (pairT gt (listT xt))
    in F.PApp2 rt (LiftedN Zero F.Group) gs xs

sort :: Expr -> Expr -> Expr
sort = $unimplemented

cons :: Expr -> Expr -> Expr
cons e1 e2 = 
    let t2 = typeOf e2
    in F.PApp2 t2 (LiftedN Zero F.Cons) e1 e2

pair :: Expr -> Expr -> Expr
pair e1 e2 = 
    let t1 = typeOf e1
        t2 = typeOf e2
        rt = pairT t1 t2
    in F.PApp2 rt (LiftedN Zero F.Pair) e1 e2

zip :: Expr -> Expr -> Expr
zip e1 e2 = 
    let t2 = typeOf e2
    in F.PApp2 t2 (LiftedN Zero F.Zip) e1 e2

cartProduct :: Expr -> Expr -> Expr
cartProduct e1 e2 = 
    let t2 = typeOf e2
    -- FIXME incorrect result type
    in F.PApp2 t2 (LiftedN Zero F.CartProduct) e1 e2
                         
nestProduct :: Expr -> Expr -> Expr
nestProduct e1 e2 = 
    let t1 = typeOf e1
        t2 = typeOf e2
        -- [a] -> [b] -> [(a, [(a, b)])]
    -- FIXME incorrect result type!
    in F.PApp2 t2 (LiftedN Zero F.NestProduct) e1 e2
                         
thetaJoin :: JoinPredicate JoinExpr  -> Expr -> Expr -> Expr
thetaJoin p e1 e2 = 
    let t1 = typeOf e1
        t2 = typeOf e2
    -- FIXME incorrect result type
    in F.PApp2 t2 (LiftedN Zero $ F.ThetaJoin p) e1 e2
                         
nestJoin :: JoinPredicate JoinExpr  -> Expr -> Expr -> Expr
nestJoin p e1 e2 = 
    let xst@(ListT xt) = typeOf e1
        yst@(ListT yt) = typeOf e2
        tr = listT $ pairT xt (listT yt)
    in F.PApp2 tr (LiftedN Zero $ F.NestJoin p) e1 e2
                         
semiJoin :: JoinPredicate JoinExpr  -> Expr -> Expr -> Expr
semiJoin p e1 e2 = 
    let t1 = typeOf e1
        t2 = typeOf e2
    in F.PApp2 t2 (LiftedN Zero $ F.SemiJoin p) e1 e2
                         
antiJoin :: JoinPredicate JoinExpr  -> Expr -> Expr -> Expr
antiJoin p e1 e2 = 
    let t1 = typeOf e1
        t2 = typeOf e2
    in F.PApp2 t2 (LiftedN Zero $ F.AntiJoin p) e1 e2
                         
append :: Expr -> Expr -> Expr
append e1 e2 = 
    let t1 = typeOf e1
        t2 = typeOf e2
    in F.PApp2 t1 (LiftedN Zero F.Append) e1 e2

index :: Expr -> Expr -> Expr
index e1 e2 = 
    let t1@(ListT t) = typeOf e1
        t2 = typeOf e2
    in F.PApp2 t (LiftedN Zero F.Index) e1 e2

length :: Expr -> Expr
length e1 = 
    let t1@(ListT _) = typeOf e1
    in F.PApp1 intT (LiftedN Zero F.Length) e1

-- FIXME this is not the right place to perform this step. If at all,
-- do it during compilation to VL.
head :: Expr -> Expr
head = the

the :: Expr -> Expr
the e1 = 
    let t1@(ListT t1') = typeOf e1
    in F.PApp1 t1' (LiftedN Zero F.The) e1

last :: Expr -> Expr
last e1 = 
    let t1@(ListT t1') = typeOf e1
    in F.PApp1 t1' (LiftedN Zero F.Last) e1

tail :: Expr -> Expr
tail e1 = 
    let t1@(ListT _) = typeOf e1
    in F.PApp1 t1 (LiftedN Zero F.Tail) e1

nub :: Expr -> Expr
nub e1 = 
    let t1@(ListT _) = typeOf e1
    in F.PApp1 t1 (LiftedN Zero F.Nub) e1

number :: Expr -> Expr
number e1 = 
    let (ListT t) = typeOf e1
        rt        = (ListT (PairT t IntT ))
    in F.PApp1 rt (LiftedN Zero F.Number) e1

init :: Expr -> Expr
init e1 = 
    let t1@(ListT _) = typeOf e1
    in F.PApp1 t1 (LiftedN Zero F.Init) e1

reverse :: Expr -> Expr
reverse e1 = 
    let t1@(ListT _) = typeOf e1
    in F.PApp1 t1 (LiftedN Zero F.Reverse) e1

and :: Expr -> Expr
and e1 = 
    let t1@(ListT BoolT) = typeOf e1
    in F.PApp1 BoolT (LiftedN Zero F.And) e1

or :: Expr -> Expr
or e1 = 
    let t1@(ListT BoolT) = typeOf e1
    in F.PApp1 BoolT (LiftedN Zero F.Or) e1

sum :: Expr -> Expr
sum e1 = 
    let t1@(ListT t) = typeOf e1
    in F.PApp1 t (LiftedN Zero F.Sum) e1
              
avg :: Expr -> Expr
avg e1 = 
    let t1 = typeOf e1
    in F.PApp1 DoubleT (LiftedN Zero F.Avg) e1

minimum :: Expr -> Expr
minimum e1 = 
    let t1@(ListT t) = typeOf e1
    in F.PApp1 t (LiftedN Zero F.Minimum) e1

maximum :: Expr -> Expr
maximum e1 = 
    let t1@(ListT t) = typeOf e1
    in F.PApp1 t (LiftedN Zero F.Maximum) e1

{-
qConcat :: Expr -> Expr
qConcat e = 
    let t1@(ListT rt@(ListT _)) = typeOf e
    in F.PApp1 rt F.QuickConcat e
-}

concat :: Expr -> Expr
concat e = 
    let t1@(ListT rt@(ListT _)) = typeOf e
    in F.PApp1 rt (LiftedN Zero F.Concat) e
                
dist :: Expr -> Expr -> Expr
dist e1 e2 = 
    let t1 = typeOf e1
        t2 = typeOf e2
    in F.PApp2 (listT t1) (LiftedN Zero F.Dist) e1 e2

restrict :: Expr -> Expr -> Expr
restrict e1 e2 = 
    let t1 = typeOf e1
        rt = t1
        ft = t1 .-> listT boolT .-> rt
    in F.PApp2 rt (LiftedN Zero F.Restrict) e1 e2

combine :: Expr -> Expr -> Expr -> Expr
combine e1 e2 e3 = 
    let t1 = typeOf e1 
        t2 = typeOf e2
        rt = t2
        ft = t1 .-> t2 .-> t2 .-> rt
    in F.PApp3 rt (LiftedN Zero F.Combine) e1 e2 e3

{-
unconcat :: Expr -> Expr -> Expr
unconcat e1 e2 = 
    let t1 = typeOf e1
        t2 = typeOf e2
        rt = listT t2
        ft = t1 .-> t2 .-> rt
    in F.PApp2 rt F.Unconcat e1 e2 
-}

intF :: Int -> Expr
intF i = F.Const intT $ IntV i

varF :: Type -> String -> Expr
varF t x = F.Var t x

fst :: Expr -> Expr
fst e = 
    let PairT t1 _ = typeOf e
    in PApp1 t1 (LiftedN Zero F.Fst) e

snd :: Expr -> Expr
snd e = 
    let PairT _ t2 = typeOf e
    in PApp1 t2 (LiftedN Zero F.Snd) e

if_ :: Expr -> Expr -> Expr -> Expr
if_ eb et ee = 
    let (BoolT, tt, te) = (typeOf eb, typeOf et, typeOf ee)
    in if tt == te
       then If tt eb et ee
       else error $ printf "FKL.if: incompatible types: %s %s" (pp tt) (pp te)

ifM :: Monad m => m Expr -> m Expr -> m Expr -> m Expr
ifM = liftM3 if_

--------------------------------------------------------------------------------
-- Smart constructors for binary and unary operators.
    
bin :: Type -> ScalarBinOp -> Expr -> Expr -> Expr     
bin t o e1 e2 = 
    case (typeOf e1, o) of
        -- FIXME implementation of equality on tuples should be
        -- performed in the frontend.
        (PairT _ _, SBRelOp Eq) -> 
            bin t (SBBoolOp Conj) (bin t (SBRelOp Eq) (fst e1) (fst e2)) 
                                  (bin t (SBRelOp Eq) (snd e1) (snd e2))
        _                       -> BinOp t (LiftedN Zero o) e1 e2

un :: Type -> ScalarUnOp -> Expr -> Expr
un t o e = UnOp t (LiftedN Zero o) e

