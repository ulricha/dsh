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
    in F.PApp1 t F.Transpose e

-- transposeL :: [[[a]]] -> [[[a]]]
transposeL :: Expr -> Expr
transposeL e = 
    let t = typeOf e
    in F.PApp1 t F.TransposeL e

-- transpose :: [a] -> [[a]]
reshape :: Integer -> Expr -> Expr
reshape n e = 
    let t = typeOf e
    in F.PApp1 (ListT t) (F.Reshape n) e

-- transpose :: [[a]] -> [[[a]]]
reshapeL :: Integer -> Expr -> Expr
reshapeL n e = 
    let t = typeOf e
    in F.PApp1 (ListT t) (F.ReshapeL n) e

group :: Expr -> Expr -> Expr
group gs xs =
    let ListT xt = typeOf xs
        ListT gt = typeOf gs
        rt             = listT (pairT gt (listT xt))
    in F.PApp2 rt F.Group gs xs

groupL :: Expr -> Expr -> Expr
groupL = $unimplemented

sort :: Expr -> Expr -> Expr
sort = $unimplemented

sortL :: Expr -> Expr -> Expr
sortL = $unimplemented

cons :: Expr -> Expr -> Expr
cons e1 e2 = 
    let t2 = typeOf e2
    in F.PApp2 t2 F.Cons e1 e2

consL :: Expr -> Expr -> Expr
consL e1 e2 =
    let t2 = typeOf e2
    in F.PApp2 t2 F.ConsL e1 e2

pair :: Expr -> Expr -> Expr
pair e1 e2 = 
    let t1 = typeOf e1
        t2 = typeOf e2
        rt = pairT t1 t2
    in F.PApp2 rt F.Pair e1 e2

-- FIXME lifted pair is equivalent to zip!
pairL :: Expr -> Expr -> Expr
pairL e1 e2 = 
    let ListT t1' = typeOf e1
        ListT t2' = typeOf e2
        rt        = listT (pairT t1' t2')
    in F.PApp2 rt F.PairL e1 e2 

zip :: Expr -> Expr -> Expr
zip e1 e2 = 
    let t2 = typeOf e2
    in F.PApp2 t2 F.Zip e1 e2

zipL :: Expr -> Expr -> Expr
zipL e1 e2 = 
    let t2@(ListT _) = typeOf e2
    in F.PApp2 t2 F.ZipL e1 e2
                  
cartProduct :: Expr -> Expr -> Expr
cartProduct e1 e2 = 
    let t2 = typeOf e2
    -- FIXME incorrect result type
    in F.PApp2 t2 F.CartProduct e1 e2
                         
cartProductL :: Expr -> Expr -> Expr
cartProductL e1 e2 = 
    let t1@(ListT t1') = typeOf e1
        t2@(ListT t2') = typeOf e2
    -- FIXME incorrect result type
    in F.PApp2 t2 F.CartProductL e1 e2

nestProduct :: Expr -> Expr -> Expr
nestProduct e1 e2 = 
    let t1 = typeOf e1
        t2 = typeOf e2
        -- [a] -> [b] -> [(a, [(a, b)])]
    -- FIXME incorrect result type!
    in F.PApp2 t2 F.NestProduct e1 e2
                         
nestProductL :: Expr -> Expr -> Expr
nestProductL e1 e2 = 
    let t1@(ListT t1') = typeOf e1
        t2@(ListT t2') = typeOf e2
     -- FIXME incorrect result type
    in F.PApp2 t2 F.NestProductL e1 e2

thetaJoin :: JoinPredicate JoinExpr  -> Expr -> Expr -> Expr
thetaJoin p e1 e2 = 
    let t1 = typeOf e1
        t2 = typeOf e2
    -- FIXME incorrect result type
    in F.PApp2 t2 (F.ThetaJoin p) e1 e2
                         
thetaJoinL :: JoinPredicate JoinExpr  -> Expr -> Expr -> Expr
thetaJoinL p e1 e2 = 
    let t1@(ListT t1') = typeOf e1
        t2@(ListT t2') = typeOf e2
    -- FIXME incorrect result type
    in F.PApp2 t2 (F.ThetaJoinL p) e1 e2

nestJoin :: JoinPredicate JoinExpr  -> Expr -> Expr -> Expr
nestJoin p e1 e2 = 
    let xst@(ListT xt) = typeOf e1
        yst@(ListT yt) = typeOf e2
        tr = listT $ pairT xt (listT yt)
    in F.PApp2 tr (F.NestJoin p) e1 e2
                         
nestJoinL :: JoinPredicate JoinExpr  -> Expr -> Expr -> Expr
nestJoinL p e1 e2 = 
    let xst@(ListT (ListT xt)) = typeOf e1
        yst@(ListT yt) = typeOf e2
        tr = listT $ listT $ pairT xt yt
    in F.PApp2 tr (F.NestJoinL p) e1 e2

semiJoin :: JoinPredicate JoinExpr  -> Expr -> Expr -> Expr
semiJoin p e1 e2 = 
    let t1 = typeOf e1
        t2 = typeOf e2
    in F.PApp2 t2 (F.SemiJoin p) e1 e2
                         
semiJoinL :: JoinPredicate JoinExpr  -> Expr -> Expr -> Expr
semiJoinL p e1 e2 = 
    let t1 = typeOf e1
        t2 = typeOf e2
    in F.PApp2 t2 (F.SemiJoinL p) e1 e2

antiJoin :: JoinPredicate JoinExpr  -> Expr -> Expr -> Expr
antiJoin p e1 e2 = 
    let t1 = typeOf e1
        t2 = typeOf e2
    in F.PApp2 t2 (F.AntiJoin p) e1 e2
                         
antiJoinL :: JoinPredicate JoinExpr  -> Expr -> Expr -> Expr
antiJoinL p e1 e2 = 
    let t1 = typeOf e1
        t2 = typeOf e2
    in F.PApp2 t2 (F.AntiJoinL p) e1 e2

append :: Expr -> Expr -> Expr
append e1 e2 = 
    let t1 = typeOf e1
        t2 = typeOf e2
    in F.PApp2 t1 F.Append e1 e2

appendL :: Expr -> Expr -> Expr
appendL e1 e2 = 
    let t1@(ListT _) = typeOf e1
        t2@(ListT _) = typeOf e2
    in F.PApp2 t1 F.AppendL e1 e2 


index :: Expr -> Expr -> Expr
index e1 e2 = 
    let t1@(ListT t) = typeOf e1
        t2 = typeOf e2
    in F.PApp2 t F.Index e1 e2

indexL :: Expr -> Expr -> Expr
indexL e1 e2 = 
    let t1@(ListT t) = typeOf e1
        t2@(ListT _) = typeOf e2
    in F.PApp2 t F.IndexL e1 e2

length :: Expr -> Expr
length e1 = 
    let t1@(ListT _) = typeOf e1
    in F.PApp1 intT F.Length e1

lengthL :: Expr -> Expr
lengthL e1 = 
    let t1@(ListT (ListT _)) = typeOf e1
    in F.PApp1 (listT intT) F.LengthL e1

-- FIXME this is not the right place to perform this step. If at all,
-- do it during compilation to VL.
head :: Expr -> Expr
head = the

headL :: Expr -> Expr
headL = theL
    
the :: Expr -> Expr
the e1 = 
    let t1@(ListT t1') = typeOf e1
    in F.PApp1 t1' F.The e1

theL :: Expr -> Expr
theL e1 = 
    let t1@(ListT t@(ListT _)) = typeOf e1
    in F.PApp1 t F.TheL e1

last :: Expr -> Expr
last e1 = 
    let t1@(ListT t1') = typeOf e1
    in F.PApp1 t1' F.Last e1

lastL :: Expr -> Expr
lastL e1 = 
    let t1@(ListT t@(ListT _)) = typeOf e1
    in F.PApp1 t F.LastL e1


tail :: Expr -> Expr
tail e1 = 
    let t1@(ListT _) = typeOf e1
    in F.PApp1 t1 F.Tail e1

tailL :: Expr -> Expr
tailL e1 = 
    let t1@(ListT (ListT _)) = typeOf e1
    in F.PApp1 t1 F.TailL e1

nub :: Expr -> Expr
nub e1 = 
    let t1@(ListT _) = typeOf e1
    in F.PApp1 t1 F.Nub e1

nubL :: Expr -> Expr
nubL e1 = 
    let t1@(ListT (ListT _)) = typeOf e1
    in F.PApp1 t1 F.NubL e1

number :: Expr -> Expr
number e1 = 
    let (ListT t) = typeOf e1
        rt        = (ListT (PairT t IntT ))
    in F.PApp1 rt F.Number e1

numberL :: Expr -> Expr
numberL e1 = 
    let t1@(ListT (ListT t)) = typeOf e1
        rt = ListT (ListT (PairT t IntT))
    in F.PApp1 rt F.NumberL e1

init :: Expr -> Expr
init e1 = 
    let t1@(ListT _) = typeOf e1
    in F.PApp1 t1 F.Init e1

initL :: Expr -> Expr
initL e1 = 
    let t1@(ListT (ListT _)) = typeOf e1
    in F.PApp1 t1 F.InitL e1

reverse :: Expr -> Expr
reverse e1 = 
    let t1@(ListT _) = typeOf e1
    in F.PApp1 t1 F.Reverse e1

reverseL :: Expr -> Expr
reverseL e1 = 
    let t1@(ListT (ListT _)) = typeOf e1
    in F.PApp1 t1 F.ReverseL e1

and :: Expr -> Expr
and e1 = 
    let t1@(ListT BoolT) = typeOf e1
    in F.PApp1 BoolT F.And e1

andL :: Expr -> Expr 
andL e1 = 
    let t1@(ListT t@(ListT BoolT)) = typeOf e1
    in F.PApp1 t F.AndL e1

or :: Expr -> Expr
or e1 = 
    let t1@(ListT BoolT) = typeOf e1
    in F.PApp1 BoolT F.Or e1

orL :: Expr -> Expr 
orL e1 = 
    let t1@(ListT t@(ListT BoolT)) = typeOf e1
    in F.PApp1 t F.OrL e1

sum :: Expr -> Expr
sum e1 = 
    let t1@(ListT t) = typeOf e1
    in F.PApp1 t F.Sum e1
              
avg :: Expr -> Expr
avg e1 = 
    let t1 = typeOf e1
    in F.PApp1 DoubleT F.Avg e1

sumL :: Expr -> Expr
sumL e1 = 
    let t1@(ListT t@(ListT _)) = typeOf e1
    in F.PApp1 t F.SumL e1
               
avgL :: Expr -> Expr
avgL e1 = 
    let t1@(ListT _) = typeOf e1
    in F.PApp1 (ListT DoubleT) F.AvgL e1

minimum :: Expr -> Expr
minimum e1 = 
    let t1@(ListT t) = typeOf e1
    in F.PApp1 t F.Minimum e1

minimumL :: Expr -> Expr
minimumL e1 = 
    let t1@(ListT t@(ListT _)) = typeOf e1
    in F.PApp1 t F.MinimumL e1

maximum :: Expr -> Expr
maximum e1 = 
    let t1@(ListT t) = typeOf e1
    in F.PApp1 t F.Maximum e1

maximumL :: Expr -> Expr
maximumL e1 = 
    let t1@(ListT t@(ListT _)) = typeOf e1
    in F.PApp1 t F.MaximumL e1

qConcat :: Expr -> Expr
qConcat e = 
    let t1@(ListT rt@(ListT _)) = typeOf e
    in F.PApp1 rt F.QuickConcat e

concat :: Expr -> Expr
concat e = 
    let t1@(ListT rt@(ListT _)) = typeOf e
    in F.PApp1 rt F.Concat e
                
concatL :: Expr -> Expr
concatL e = 
    let t1@(ListT rt@(ListT (ListT _))) = typeOf e
    in F.PApp1 rt F.ConcatL e

dist :: Expr -> Expr -> Expr
dist e1 e2 = 
    let t1 = typeOf e1
        t2 = typeOf e2
    in F.PApp2 (listT t1) F.Dist e1 e2

distL :: Expr -> Expr -> Expr
distL e1 e2 = 
    let t1 = typeOf e1
        t2 = typeOf e2
        ft = t1 .-> t2 .-> listT t1
    in F.PApp2 (listT t1) F.DistL e1 e2

restrict :: Expr -> Expr -> Expr
restrict e1 e2 = 
    let t1 = typeOf e1
        rt = t1
        ft = t1 .-> listT boolT .-> rt
    in F.PApp2 rt F.Restrict e1 e2

restrictL :: Expr -> Expr -> Expr
restrictL = $unimplemented

combine :: Expr -> Expr -> Expr -> Expr
combine e1 e2 e3 = 
    let t1 = typeOf e1 
        t2 = typeOf e2
        rt = t2
        ft = t1 .-> t2 .-> t2 .-> rt
    in F.PApp3 rt F.Combine e1 e2 e3

unconcat :: Expr -> Expr -> Expr
unconcat e1 e2 = 
    let t1 = typeOf e1
        t2 = typeOf e2
        rt = listT t2
        ft = t1 .-> t2 .-> rt
    in F.PApp2 rt F.Unconcat e1 e2 

intF :: Int -> Expr
intF i = F.Const intT $ IntV i

varF :: Type -> String -> Expr
varF t x = F.Var t x

fst :: Expr -> Expr
fst e = 
    let PairT t1 _ = typeOf e
    in PApp1 t1 F.Fst e

snd :: Expr -> Expr
snd e = 
    let PairT _ t2 = typeOf e
    in PApp1 t2 F.Snd e

fstL :: Expr -> Expr
fstL e = 
    let t@(ListT (PairT t1 _)) = typeOf e
    in PApp1 (ListT t1) F.FstL e

sndL :: Expr -> Expr
sndL e = 
    let t@(ListT (PairT _ t2)) = typeOf e
    in PApp1 (ListT t2) F.SndL e

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
        _                            -> BinOp t (NotLifted o) e1 e2

binM :: Monad m => Type -> ScalarBinOp -> m Expr -> m Expr -> m Expr
binM t o = liftM2 (bin t o)

binL :: Type -> ScalarBinOp -> Expr -> Expr -> Expr
binL t o = BinOp (liftType t) (Lifted o) 

binLM :: Monad m => Type -> ScalarBinOp -> m Expr -> m Expr -> m Expr
binLM t o = liftM2 (binL t o)

un :: Type -> ScalarUnOp -> Expr -> Expr
un t o e = UnOp t (NotLifted o) e

unM :: Monad m => Type -> ScalarUnOp -> m Expr -> m Expr
unM t o = liftM (un t o)

unL :: Type -> ScalarUnOp -> Expr -> Expr
unL t o e = UnOp (liftType t) (Lifted o) e

unLM :: Monad m => Type -> ScalarUnOp -> m Expr -> m Expr
unLM t o = liftM (unL t o)

