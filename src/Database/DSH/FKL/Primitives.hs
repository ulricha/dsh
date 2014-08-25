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
    in F.PApp1 t (F.Transpose (t .-> t)) e

-- transposeL :: [[[a]]] -> [[[a]]]
transposeL :: Expr -> Expr
transposeL e = 
    let t = typeOf e
    in F.PApp1 t (F.TransposeL (t .-> t)) e

-- transpose :: [a] -> [[a]]
reshape :: Integer -> Expr -> Expr
reshape n e = 
    let t = typeOf e
    in F.PApp1 (ListT t) (F.Reshape n (t .-> ListT t)) e

-- transpose :: [[a]] -> [[[a]]]
reshapeL :: Integer -> Expr -> Expr
reshapeL n e = 
    let t = typeOf e
    in F.PApp1 (ListT t) (F.ReshapeL n (t .-> ListT t)) e

group :: Expr -> Expr -> Expr
group gs xs =
    let xst@(ListT xt) = typeOf xs
        gst@(ListT gt) = typeOf gs
        rt             = listT (pairT gt (listT xt))
    in F.PApp2 rt (F.Group $ gst .-> xst .-> rt) gs xs

groupL :: Expr -> Expr -> Expr
groupL = $unimplemented

sort :: Expr -> Expr -> Expr
sort = $unimplemented

sortL :: Expr -> Expr -> Expr
sortL = $unimplemented


{-
groupWithKey :: Expr -> Expr -> Expr
groupWithKey f e = let arg1 = map f e
                           t1@(FunT _ tk) = typeOf arg1
                           t2           = typeOf e
                           t3           = listT $ pairT tk t2
                       in F.PApp2 t3 (F.GroupWithKey (t1 .-> t2 .-> t3)) arg1 e

groupWithKeyL :: Expr -> Expr -> Expr
groupWithKeyL f e = let arg1 = mapL f e
                            t1@(FunT _ tk) = typeOf arg1 
                            t2           = typeOf e
                            t3           = listT $ pairT tk t2
                        in F.PApp2 t3 (F.GroupWithKeyL (t1 .-> t2 .-> t3)) arg1 e 
-}

cons :: Expr -> Expr -> Expr
cons e1 e2 = 
    let t1 = typeOf e1
        t2 = typeOf e2
    in F.PApp2 t2 (F.Cons (t1 .-> t2 .-> t2)) e1 e2

consL :: Expr -> Expr -> Expr
consL e1 e2 =
    let t1 = typeOf e1
        t2 = typeOf e2
    in F.PApp2 t2 (F.ConsL (t1 .-> t2 .-> t2)) e1 e2


pair :: Expr -> Expr -> Expr
pair e1 e2 = 
    let t1 = typeOf e1
        t2 = typeOf e2
        rt = pairT t1 t2
    in F.PApp2 rt (F.Pair (t1 .-> t2 .-> rt)) e1 e2

-- FIXME lifted pair is equivalent to zip!
pairL :: Expr -> Expr -> Expr
pairL e1 e2 = 
    let t1@(ListT t1') = typeOf e1
        t2@(ListT t2') = typeOf e2
        rt = listT (pairT t1' t2')
    in F.PApp2 rt (F.PairL (t1 .-> t2 .-> rt)) e1 e2 

zip :: Expr -> Expr -> Expr
zip e1 e2 = 
    let t1 = typeOf e1
        t2 = typeOf e2
    in F.PApp2 t2 (F.Zip (t1 .-> t2 .-> PairT t1 t2)) e1 e2

zipL :: Expr -> Expr -> Expr
zipL e1 e2 = 
    let t1@(ListT t1') = typeOf e1
        t2@(ListT t2') = typeOf e2
    in F.PApp2 t2 (F.ZipL (t1 .-> t2 .-> listT (PairT t1' t2'))) e1 e2
                  
cartProduct :: Expr -> Expr -> Expr
cartProduct e1 e2 = 
    let t1 = typeOf e1
        t2 = typeOf e2
    in F.PApp2 t2 (F.CartProduct (t1 .-> t2 .-> PairT t1 t2)) e1 e2
                         
cartProductL :: Expr -> Expr -> Expr
cartProductL e1 e2 = 
    let t1@(ListT t1') = typeOf e1
        t2@(ListT t2') = typeOf e2
    in F.PApp2 t2 (F.CartProductL (t1 .-> t2 .-> listT (PairT t1' t2'))) e1 e2

nestProduct :: Expr -> Expr -> Expr
nestProduct e1 e2 = 
    let t1 = typeOf e1
        t2 = typeOf e2
        -- [a] -> [b] -> [(a, [(a, b)])]
    in F.PApp2 t2 (F.NestProduct (t1 .-> t2 .-> PairT t1 t2)) e1 e2
                         
nestProductL :: Expr -> Expr -> Expr
nestProductL e1 e2 = 
    let t1@(ListT t1') = typeOf e1
        t2@(ListT t2') = typeOf e2
    in F.PApp2 t2 (F.NestProductL (t1 .-> t2 .-> listT (PairT t1' t2'))) e1 e2

thetaJoin :: JoinPredicate JoinExpr  -> Expr -> Expr -> Expr
thetaJoin p e1 e2 = 
    let t1 = typeOf e1
        t2 = typeOf e2
    in F.PApp2 t2 (F.ThetaJoin p (t1 .-> t2 .-> PairT t1 t2)) e1 e2
                         
thetaJoinL :: JoinPredicate JoinExpr  -> Expr -> Expr -> Expr
thetaJoinL p e1 e2 = 
    let t1@(ListT t1') = typeOf e1
        t2@(ListT t2') = typeOf e2
    in F.PApp2 t2 (F.ThetaJoinL p (t1 .-> t2 .-> listT (PairT t1' t2'))) e1 e2

nestJoin :: JoinPredicate JoinExpr  -> Expr -> Expr -> Expr
nestJoin p e1 e2 = 
    let xst@(ListT xt) = typeOf e1
        yst@(ListT yt) = typeOf e2
        tr = listT $ pairT xt (listT yt)
    in F.PApp2 tr (F.NestJoin p (xst .-> yst .-> tr)) e1 e2
                         
nestJoinL :: JoinPredicate JoinExpr  -> Expr -> Expr -> Expr
nestJoinL p e1 e2 = 
    let xst@(ListT (ListT xt)) = typeOf e1
        yst@(ListT yt) = typeOf e2
        tr = listT $ listT $ pairT xt yt
    in F.PApp2 tr (F.NestJoinL p (xst .-> yst .-> tr)) e1 e2

semiJoin :: JoinPredicate JoinExpr  -> Expr -> Expr -> Expr
semiJoin p e1 e2 = 
    let t1 = typeOf e1
        t2 = typeOf e2
    in F.PApp2 t2 (F.SemiJoin p (t1 .-> t2 .-> t1)) e1 e2
                         
semiJoinL :: JoinPredicate JoinExpr  -> Expr -> Expr -> Expr
semiJoinL p e1 e2 = 
    let t1 = typeOf e1
        t2 = typeOf e2
    in F.PApp2 t2 (F.SemiJoinL p (t1 .-> t2 .-> t1)) e1 e2

antiJoin :: JoinPredicate JoinExpr  -> Expr -> Expr -> Expr
antiJoin p e1 e2 = 
    let t1 = typeOf e1
        t2 = typeOf e2
    in F.PApp2 t2 (F.AntiJoin p (t1 .-> t2 .-> t1)) e1 e2
                         
antiJoinL :: JoinPredicate JoinExpr  -> Expr -> Expr -> Expr
antiJoinL p e1 e2 = 
    let t1 = typeOf e1
        t2 = typeOf e2
    in F.PApp2 t2 (F.AntiJoinL p (t1 .-> t2 .-> t1)) e1 e2

append :: Expr -> Expr -> Expr
append e1 e2 = 
    let t1 = typeOf e1
        t2 = typeOf e2
    in F.PApp2 t1 (F.Append (t1 .-> t2 .-> t1)) e1 e2

appendL :: Expr -> Expr -> Expr
appendL e1 e2 = 
    let t1@(ListT _) = typeOf e1
        t2@(ListT _) = typeOf e2
    in F.PApp2 t1 (F.AppendL (t1 .-> t2 .-> t1)) e1 e2 


index :: Expr -> Expr -> Expr
index e1 e2 = 
    let t1@(ListT t) = typeOf e1
        t2 = typeOf e2
    in F.PApp2 t (F.Index (t1 .-> t2 .-> t)) e1 e2

indexL :: Expr -> Expr -> Expr
indexL e1 e2 = 
    let t1@(ListT t) = typeOf e1
        t2@(ListT _) = typeOf e2
    in F.PApp2 t (F.IndexL (t1 .-> t2 .-> t)) e1 e2

{-
filter :: Expr -> Expr -> Expr
filter f e = let arg1 = map f e
                  in restrict e arg1
-}
                  
{-
filterL :: Expr -> Expr -> Expr
filterL f e = let arg1 = qConcat (mapL f e)
                   in unconcat e (restrict (qConcat e) arg1)
-}

--The sortWith combinator

{-
sortWith :: Expr -> Expr -> Expr
sortWith f e = let arg1 = map f e
                       t1@(ListT _) = typeOf arg1
                       t2@(ListT _) = typeOf e
                    in F.PApp2 t2 (F.SortWithS (t1 .-> t2 .-> t2)) arg1 e

sortWithL :: Expr -> Expr -> Expr
sortWithL f e = let arg1 = mapL f e
                        t1@(ListT (ListT _)) = typeOf arg1 
                        t2@(ListT (ListT _)) = typeOf e
                     in F.PApp2 t2 (F.SortWithL (t1 .-> t2 .-> t2)) arg1 e
-}

length :: Expr -> Expr
length e1 = 
    let t1@(ListT _) = typeOf e1
    in F.PApp1 intT (F.Length $ t1 .-> intT) e1

lengthL :: Expr -> Expr
lengthL e1 = 
    let t1@(ListT (ListT _)) = typeOf e1
    in F.PApp1 (listT intT) (F.LengthL $ t1 .-> listT intT) e1

-- FIXME this is not the right place to perform this step. If at all,
-- do it during compilation to VL.
head :: Expr -> Expr
head = the

headL :: Expr -> Expr
headL = theL
    
the :: Expr -> Expr
the e1 = 
    let t1@(ListT t1') = typeOf e1
    in F.PApp1 t1' (F.The $ t1 .-> t1') e1

theL :: Expr -> Expr
theL e1 = 
    let t1@(ListT t@(ListT _)) = typeOf e1
    in F.PApp1 t (F.TheL $ t1 .-> t) e1

last :: Expr -> Expr
last e1 = 
    let t1@(ListT t1') = typeOf e1
    in F.PApp1 t1' (F.Last $ t1 .-> t1') e1

lastL :: Expr -> Expr
lastL e1 = 
    let t1@(ListT t@(ListT _)) = typeOf e1
    in F.PApp1 t (F.LastL $ t1 .-> t) e1


tail :: Expr -> Expr
tail e1 = 
    let t1@(ListT _) = typeOf e1
    in F.PApp1 t1 (F.Tail $ t1 .-> t1) e1

tailL :: Expr -> Expr
tailL e1 = 
    let t1@(ListT (ListT _)) = typeOf e1
    in F.PApp1 t1 (F.TailL $ t1 .-> t1) e1

nub :: Expr -> Expr
nub e1 = 
    let t1@(ListT _) = typeOf e1
    in F.PApp1 t1 (F.Nub $ t1 .-> t1) e1

nubL :: Expr -> Expr
nubL e1 = 
    let t1@(ListT (ListT _)) = typeOf e1
    in F.PApp1 t1 (F.NubL $ t1 .-> t1) e1

number :: Expr -> Expr
number e1 = 
    let (ListT t) = typeOf e1
        rt        = (ListT (PairT t IntT ))
        ft        = (ListT t) .-> (ListT (PairT t IntT ))
    in F.PApp1 rt (F.Number ft) e1

numberL :: Expr -> Expr
numberL e1 = 
    let t1@(ListT (ListT t)) = typeOf e1
        rt = ListT (ListT (PairT t IntT))
    in F.PApp1 rt (F.NumberL $ t1 .-> rt) e1

init :: Expr -> Expr
init e1 = 
    let t1@(ListT _) = typeOf e1
    in F.PApp1 t1 (F.Init $ t1 .-> t1) e1

initL :: Expr -> Expr
initL e1 = 
    let t1@(ListT (ListT _)) = typeOf e1
    in F.PApp1 t1 (F.InitL $ t1 .-> t1) e1

reverse :: Expr -> Expr
reverse e1 = 
    let t1@(ListT _) = typeOf e1
    in F.PApp1 t1 (F.Reverse $ t1 .-> t1) e1

reverseL :: Expr -> Expr
reverseL e1 = 
    let t1@(ListT (ListT _)) = typeOf e1
    in F.PApp1 t1 (F.ReverseL $ t1 .-> t1) e1

and :: Expr -> Expr
and e1 = 
    let t1@(ListT BoolT) = typeOf e1
    in F.PApp1 BoolT (F.And $ t1 .-> BoolT) e1

andL :: Expr -> Expr 
andL e1 = 
    let t1@(ListT t@(ListT BoolT)) = typeOf e1
    in F.PApp1 t (F.AndL $ t1 .-> t) e1


or :: Expr -> Expr
or e1 = 
    let t1@(ListT BoolT) = typeOf e1
    in F.PApp1 BoolT (F.Or $ t1 .-> BoolT) e1

orL :: Expr -> Expr 
orL e1 = 
    let t1@(ListT t@(ListT BoolT)) = typeOf e1
    in F.PApp1 t (F.OrL $ t1 .-> t) e1

sum :: Expr -> Expr
sum e1 = 
    let t1@(ListT t) = typeOf e1
    in F.PApp1 t (F.Sum $ t1 .-> t) e1
              
avg :: Expr -> Expr
avg e1 = 
    let t1 = typeOf e1
    in F.PApp1 DoubleT (F.Avg $ t1 .-> DoubleT) e1

sumL :: Expr -> Expr
sumL e1 = 
    let t1@(ListT t@(ListT _)) = typeOf e1
    in F.PApp1 t (F.SumL $ t1 .-> t) e1
               
avgL :: Expr -> Expr
avgL e1 = 
    let t1@(ListT _) = typeOf e1
    in F.PApp1 (ListT DoubleT) (F.AvgL $ t1 .-> (ListT DoubleT)) e1

minimum :: Expr -> Expr
minimum e1 = 
    let t1@(ListT t) = typeOf e1
    in F.PApp1 t (F.Minimum $ t1 .-> t) e1

minimumL :: Expr -> Expr
minimumL e1 = 
    let t1@(ListT t@(ListT _)) = typeOf e1
    in F.PApp1 t (F.MinimumL $ t1 .-> t) e1

maximum :: Expr -> Expr
maximum e1 = 
    let t1@(ListT t) = typeOf e1
    in F.PApp1 t (F.Maximum $ t1 .-> t) e1

maximumL :: Expr -> Expr
maximumL e1 = 
    let t1@(ListT t@(ListT _)) = typeOf e1
    in F.PApp1 t (F.MaximumL $ t1 .-> t) e1

qConcat :: Expr -> Expr
qConcat e = 
    let t1@(ListT rt@(ListT _)) = typeOf e
        ft = t1 .-> rt
    in F.PApp1 rt (F.QuickConcat ft) e

concat :: Expr -> Expr
concat e = 
    let t1@(ListT rt@(ListT _)) = typeOf e
        ft = t1 .-> rt
    in F.PApp1 rt (F.Concat ft) e
                
concatL :: Expr -> Expr
concatL e = 
    let t1@(ListT rt@(ListT (ListT _))) = typeOf e
        ft = t1 .-> rt
    in F.PApp1 rt (F.ConcatL $ ft) e

dist :: Expr -> Expr -> Expr
dist e1 e2 = 
    let t1 = typeOf e1
        t2 = typeOf e2
        ft = t1 .-> t2 .-> listT t1
    in F.PApp2 (listT t1) (F.Dist ft) e1 e2

distL :: Expr -> Expr -> Expr
distL e1 e2 = 
    let t1 = typeOf e1
        t2 = typeOf e2
        ft = t1 .-> t2 .-> listT t1
    in F.PApp2 (listT t1) (F.DistL ft) e1 e2

restrict :: Expr -> Expr -> Expr
restrict e1 e2 = 
    let t1 = typeOf e1
        rt = t1
        ft = t1 .-> listT boolT .-> rt
    in F.PApp2 rt (F.Restrict ft) e1 e2

restrictL :: Expr -> Expr -> Expr
restrictL = $unimplemented

combine :: Expr -> Expr -> Expr -> Expr
combine e1 e2 e3 = 
    let t1 = typeOf e1 
        t2 = typeOf e2
        rt = t2
        ft = t1 .-> t2 .-> t2 .-> rt
    in F.PApp3 rt (F.Combine ft) e1 e2 e3

unconcat :: Expr -> Expr -> Expr
unconcat e1 e2 = 
    let t1 = typeOf e1
        t2 = typeOf e2
        rt = listT t2
        ft = t1 .-> t2 .-> rt
    in F.PApp2 rt (F.Unconcat ft) e1 e2 

intF :: Int -> Expr
intF i = F.Const intT $ IntV i

varF :: Type -> String -> Expr
varF t x = F.Var t x

fst :: Expr -> Expr
fst e = 
    let PairT t1 _ = typeOf e
    in PApp1 t1 (F.Fst $ typeOf e .-> t1) e

snd :: Expr -> Expr
snd e = 
    let PairT _ t2 = typeOf e
    in PApp1 t2 (F.Snd $ typeOf e .-> t2) e

fstL :: Expr -> Expr
fstL e = 
    let t@(ListT (PairT t1 _)) = typeOf e
    in PApp1 (ListT t1) (F.FstL $ t .-> ListT t1) e

sndL :: Expr -> Expr
sndL e = 
    let t@(ListT (PairT _ t2)) = typeOf e
    in PApp1 (ListT t2) (F.SndL $ t .-> ListT t2) e

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
binL t o = BinOp t (Lifted o) 

binLM :: Monad m => Type -> ScalarBinOp -> m Expr -> m Expr -> m Expr
binLM t o = liftM2 (binL t o)

un :: Type -> ScalarUnOp -> Expr -> Expr
un t o e = UnOp t (NotLifted o) e

unM :: Monad m => Type -> ScalarUnOp -> m Expr -> m Expr
unM t o = liftM (un t o)

unL :: Type -> ScalarUnOp -> Expr -> Expr
unL t o e = UnOp t (Lifted o) e

unLM :: Monad m => Type -> ScalarUnOp -> m Expr -> m Expr
unLM t o = liftM (unL t o)

