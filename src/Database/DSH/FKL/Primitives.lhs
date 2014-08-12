\newpage
%{
%include fkl.fmt
%include setQual.fmt
%include fklQual.fmt
\chapter{Functions in the flat languages}

In this chapter we describe how our primitive functions are encoded. Most
notable function of which is the map function. The flattening transformation is
aimed at removing all occurrences of this function and in particular nested
occurrences as to exploit potential parallelism. We describe a version of this
particular function that transforms function and values as described in the
previous section in both normal and nested occurrences.

%if False
\begin{code}
{-
Module containing some primitive operations in AST form.

All of these are helper functions for the flattening transformation
-}
module Database.DSH.FKL.Primitives where
       
import Database.DSH.FKL.Lang       as F
import Database.DSH.Common.Pretty
import Database.DSH.Common.Lang
import Database.DSH.Common.Type

import Control.Monad
\end{code}
%endif

The map combinator is build up out of multiple nested closures. This comes from
the fact that the function map takes two arguments (a function and a list value)
and can be applied partially. The result of a partial application can also be
manipulated as an ordinary value.

\begin{code}
mapVal :: Type -> Expr
mapVal t = doubleArgClo t "map_f" "map_xs" mapPrim mapLPrim 

mapPrim :: Expr -> Expr -> Expr
mapPrim f e = cloLApp (distPrim f e) e

mapLPrim :: Expr -> Expr -> Expr
mapLPrim f e = unconcatPrim e $ cloLApp (qConcatPrim (distLPrim f e)) (qConcatPrim e)
\end{code}

\begin{code}
--The groupWith combinator

doubleArgClo :: Type -> String -> String -> (Expr -> Expr -> Expr) -> (Expr -> Expr -> Expr) -> Expr
doubleArgClo t v1 v2 e1 e2 = Clo t "n" [] arg1 f1 f2
    where
        (t1, r1) = splitType t
        (t2, _) = splitType r1
        arg1 = "__*" ++ v1 ++ "*"
        arg2 = "__*" ++ v2 ++ "*"
        body1 = e1 (F.Var t1 arg1) (F.Var t2 arg2)
        body2 = e2 (F.Var (liftType t1) arg1) (F.Var (liftType t2) arg2)
        f1 = Clo r1 "n" [arg1] arg2 body1 body2
        f2 = AClo (liftType r1) "n" [arg1] arg2 body1 body2

transposeVal :: Type -> Expr
transposeVal t = singleArgClo t "transpose" transposePrim transposeLPrim

-- tranposePrim :: [[a]] -> [[a]]
transposePrim :: Expr -> Expr
transposePrim e = 
    let t = typeOf e 
    in F.PApp1 t (F.FTranspose (t .-> t)) e

-- transposeLPrim :: [[[a]]] -> [[[a]]]
transposeLPrim :: Expr -> Expr
transposeLPrim e = 
    let t = typeOf e
    in F.PApp1 t (F.FTransposeL (t .-> t)) e

reshapeVal :: Integer -> Type -> Expr
reshapeVal n t = singleArgClo t "reshape" (reshapePrim n) (reshapeLPrim n)

-- transpose :: [a] -> [[a]]
reshapePrim :: Integer -> Expr -> Expr
reshapePrim n e = 
    let t = typeOf e
    in F.PApp1 (ListT t) (F.FReshape n (t .-> ListT t)) e

-- transpose :: [[a]] -> [[[a]]]
reshapeLPrim :: Integer -> Expr -> Expr
reshapeLPrim n e = 
    let t = typeOf e
    in F.PApp1 (ListT t) (F.FReshapeL n (t .-> ListT t)) e

groupWithKeyVal :: Type -> Expr
groupWithKeyVal t = doubleArgClo t "group_f" "group_xs" groupWithKeyPrim groupWithKeyLPrim

groupWithKeyPrim :: Expr -> Expr -> Expr
groupWithKeyPrim f e = let arg1 = mapPrim f e
                           t1@(FunT _ tk) = typeOf arg1
                           t2           = typeOf e
                           t3           = listT $ pairT tk t2
                       in F.PApp2 t3 (F.FGroupWithKey (t1 .-> t2 .-> t3)) arg1 e

groupWithKeyLPrim :: Expr -> Expr -> Expr
groupWithKeyLPrim f e = let arg1 = mapLPrim f e
                            t1@(FunT _ tk) = typeOf arg1 
                            t2           = typeOf e
                            t3           = listT $ pairT tk t2
                        in F.PApp2 t3 (F.FGroupWithKeyL (t1 .-> t2 .-> t3)) arg1 e 

consVal :: Type -> Expr
consVal t = doubleArgClo t "cons_e1" "cons_e2" consPrim consLPrim

consPrim :: Expr -> Expr -> Expr
consPrim e1 e2 = 
    let t1 = typeOf e1
        t2 = typeOf e2
    in F.PApp2 t2 (F.FCons (t1 .-> t2 .-> t2)) e1 e2

consLPrim :: Expr -> Expr -> Expr
consLPrim e1 e2 =
    let t1 = typeOf e1
        t2 = typeOf e2
    in F.PApp2 t2 (F.FConsL (t1 .-> t2 .-> t2)) e1 e2


pairVal :: Type -> Expr
pairVal t = doubleArgClo t "pair_e1" "pair_e2" pairPrim pairLPrim

pairPrim :: Expr -> Expr -> Expr
pairPrim e1 e2 = let t1 = typeOf e1
                     t2 = typeOf e2
                     rt = pairT t1 t2
                  in F.PApp2 rt (F.FPair (t1 .-> t2 .-> rt)) e1 e2

-- FIXME lifted pair is thetavalent to zip!
pairLPrim :: Expr -> Expr -> Expr
pairLPrim e1 e2 = let t1@(ListT t1') = typeOf e1
                      t2@(ListT t2') = typeOf e2
                      rt = listT (pairT t1' t2')
                   in F.PApp2 rt (F.FPairL (t1 .-> t2 .-> rt)) e1 e2 

zipVal :: Type -> Expr
zipVal t = doubleArgClo t "zip_e1" "zip_e2" zipPrim zipLPrim

zipPrim :: Expr -> Expr -> Expr
zipPrim e1 e2 = let t1 = typeOf e1
                    t2 = typeOf e2
                 in F.PApp2 t2 (F.FZip (t1 .-> t2 .-> PairT t1 t2)) e1 e2

zipLPrim :: Expr -> Expr -> Expr
zipLPrim e1 e2 = let t1@(ListT t1') = typeOf e1
                     t2@(ListT t2') = typeOf e2
                  in F.PApp2 t2 (F.FZipL (t1 .-> t2 .-> listT (PairT t1' t2'))) e1 e2
                  
-- Types for join/product operators are mostly rubbish.
cartProductVal :: Type -> Expr
cartProductVal t = doubleArgClo t "cartProduct_e1" "cartProduct_e2" cartProductPrim cartProductLPrim
                  
cartProductPrim :: Expr -> Expr -> Expr
cartProductPrim e1 e2 = let t1 = typeOf e1
                            t2 = typeOf e2
                         in F.PApp2 t2 (F.FCartProduct (t1 .-> t2 .-> PairT t1 t2)) e1 e2
                         
cartProductLPrim :: Expr -> Expr -> Expr
cartProductLPrim e1 e2 = let t1@(ListT t1') = typeOf e1
                             t2@(ListT t2') = typeOf e2
                          in F.PApp2 t2 (F.FCartProductL (t1 .-> t2 .-> listT (PairT t1' t2'))) e1 e2

nestProductVal :: Type -> Expr
nestProductVal t = doubleArgClo t "nestProduct_e1" "nestProduct_e2" nestProductPrim nestProductLPrim
                  
nestProductPrim :: Expr -> Expr -> Expr
nestProductPrim e1 e2 = let t1 = typeOf e1
                            t2 = typeOf e2
                         -- [a] -> [b] -> [(a, [(a, b)])]
                         in F.PApp2 t2 (F.FNestProduct (t1 .-> t2 .-> PairT t1 t2)) e1 e2
                         
nestProductLPrim :: Expr -> Expr -> Expr
nestProductLPrim e1 e2 = let t1@(ListT t1') = typeOf e1
                             t2@(ListT t2') = typeOf e2
                          in F.PApp2 t2 (F.FNestProductL (t1 .-> t2 .-> listT (PairT t1' t2'))) e1 e2

thetaJoinVal :: JoinPredicate JoinExpr  -> Type -> Expr
thetaJoinVal p t = doubleArgClo t "thetaJoin_e1" "thetaJoin_e2" (thetaJoinPrim p) (thetaJoinLPrim p)
                  
thetaJoinPrim :: JoinPredicate JoinExpr  -> Expr -> Expr -> Expr
thetaJoinPrim p e1 e2 = let t1 = typeOf e1
                            t2 = typeOf e2
                        in F.PApp2 t2 (F.FThetaJoin p (t1 .-> t2 .-> PairT t1 t2)) e1 e2
                         
thetaJoinLPrim :: JoinPredicate JoinExpr  -> Expr -> Expr -> Expr
thetaJoinLPrim p e1 e2 = let t1@(ListT t1') = typeOf e1
                             t2@(ListT t2') = typeOf e2
                         in F.PApp2 t2 (F.FThetaJoinL p (t1 .-> t2 .-> listT (PairT t1' t2'))) e1 e2

nestJoinVal :: JoinPredicate JoinExpr  -> Type -> Expr
nestJoinVal p t = doubleArgClo t "nestJoin_e1" "nestJoin_e2" (nestJoinPrim p) (nestJoinLPrim p)
                  
nestJoinPrim :: JoinPredicate JoinExpr  -> Expr -> Expr -> Expr
nestJoinPrim p e1 e2 = let xst@(ListT xt) = typeOf e1
                           yst@(ListT yt) = typeOf e2
                           tr = listT $ pairT xt (listT yt)
                       in F.PApp2 tr (F.FNestJoin p (xst .-> yst .-> tr)) e1 e2
                         
nestJoinLPrim :: JoinPredicate JoinExpr  -> Expr -> Expr -> Expr
nestJoinLPrim p e1 e2 = let xst@(ListT (ListT xt)) = typeOf e1
                            yst@(ListT yt) = typeOf e2
                            tr = listT $ listT $ pairT xt yt
                        in F.PApp2 tr (F.FNestJoinL p (xst .-> yst .-> tr)) e1 e2

semiJoinVal :: JoinPredicate JoinExpr  -> Type -> Expr
semiJoinVal p t = doubleArgClo t "semiJoin_e1" "semiJoin_e2" (semiJoinPrim p) (semiJoinLPrim p)
                  
semiJoinPrim :: JoinPredicate JoinExpr  -> Expr -> Expr -> Expr
semiJoinPrim p e1 e2 = let t1 = typeOf e1
                           t2 = typeOf e2
                       in F.PApp2 t2 (F.FSemiJoin p (t1 .-> t2 .-> t1)) e1 e2
                         
semiJoinLPrim :: JoinPredicate JoinExpr  -> Expr -> Expr -> Expr
semiJoinLPrim p e1 e2 = let t1 = typeOf e1
                            t2 = typeOf e2
                        in F.PApp2 t2 (F.FSemiJoinL p (t1 .-> t2 .-> t1)) e1 e2

antiJoinVal :: JoinPredicate JoinExpr  -> Type -> Expr
antiJoinVal p t = doubleArgClo t "antiJoin_e1" "antiJoin_e2" (antiJoinPrim p) (antiJoinLPrim p)
                  
antiJoinPrim :: JoinPredicate JoinExpr  -> Expr -> Expr -> Expr
antiJoinPrim p e1 e2 = let t1 = typeOf e1
                           t2 = typeOf e2
                       in F.PApp2 t2 (F.FAntiJoin p (t1 .-> t2 .-> t1)) e1 e2
                         
antiJoinLPrim :: JoinPredicate JoinExpr  -> Expr -> Expr -> Expr
antiJoinLPrim p e1 e2 = let t1 = typeOf e1
                            t2 = typeOf e2
                        in F.PApp2 t2 (F.FAntiJoinL p (t1 .-> t2 .-> t1)) e1 e2

appendVal :: Type -> Expr
appendVal t = doubleArgClo t "append_e1" "append_e2" appendPrim appendLPrim

appendPrim :: Expr -> Expr -> Expr
appendPrim e1 e2 = let t1 = typeOf e1
                       t2 = typeOf e2
                 in F.PApp2 t1 (F.FAppend (t1 .-> t2 .-> t1)) e1 e2

appendLPrim :: Expr -> Expr -> Expr
appendLPrim e1 e2 = let t1@(ListT _) = typeOf e1
                        t2@(ListT _) = typeOf e2
                  in F.PApp2 t1 (F.FAppendL (t1 .-> t2 .-> t1)) e1 e2 


indexVal :: Type -> Expr
indexVal t = doubleArgClo t "index_e1" "index_e2" indexPrim indexLPrim

indexPrim :: Expr -> Expr -> Expr
indexPrim e1 e2 = let t1@(ListT t) = typeOf e1
                      t2 = typeOf e2
                   in F.PApp2 t (F.FIndex (t1 .-> t2 .-> t)) e1 e2

indexLPrim :: Expr -> Expr -> Expr
indexLPrim e1 e2 = let t1@(ListT t) = typeOf e1
                       t2@(ListT _) = typeOf e2
                    in F.PApp2 t (F.FIndexL (t1 .-> t2 .-> t)) e1 e2

filterVal :: Type -> Expr
filterVal t = doubleArgClo t "filter_f" "filter_xs" filterPrim filterLPrim

filterPrim :: Expr -> Expr -> Expr
filterPrim f e = let arg1 = mapPrim f e
                  in restrictPrim e arg1
                  
filterLPrim :: Expr -> Expr -> Expr
filterLPrim f e = let arg1 = qConcatPrim (mapLPrim f e)
                   in unconcatPrim e (restrictPrim (qConcatPrim e) arg1)

--The sortWith combinator

sortWithVal :: Type -> Expr
sortWithVal t = doubleArgClo t "sort_f" "sort_xs" sortWithPrim sortWithLPrim 

sortWithPrim :: Expr -> Expr -> Expr
sortWithPrim f e = let arg1 = mapPrim f e
                       t1@(ListT _) = typeOf arg1
                       t2@(ListT _) = typeOf e
                    in F.PApp2 t2 (F.FSortWithS (t1 .-> t2 .-> t2)) arg1 e

sortWithLPrim :: Expr -> Expr -> Expr
sortWithLPrim f e = let arg1 = mapLPrim f e
                        t1@(ListT (ListT _)) = typeOf arg1 
                        t2@(ListT (ListT _)) = typeOf e
                     in F.PApp2 t2 (F.FSortWithL (t1 .-> t2 .-> t2)) arg1 e

singleArgClo :: Type -> String -> (Expr -> Expr) -> (Expr -> Expr) -> Expr
singleArgClo t arg e1 e2 = Clo t "n" [] argname f1 f2
    where
        argname = "__*" ++ arg ++ "*"
        (a, _) = splitType t
        f1 = e1 (F.Var a argname)
        f2 = e2 (F.Var (liftType a) argname)  

lengthVal :: Type -> Expr
lengthVal t = singleArgClo t "length_v" lengthPrim lengthLPrim

lengthPrim :: Expr -> Expr
lengthPrim e1 = let t1@(ListT _) = typeOf e1
                 in F.PApp1 intT (F.FLength $ t1 .-> intT) e1

lengthLPrim :: Expr -> Expr
lengthLPrim e1 = let t1@(ListT (ListT _)) = typeOf e1
                  in F.PApp1 (listT intT) (F.FLengthL $ t1 .-> listT intT) e1
    
headVal :: Type -> Expr
headVal = theVal

theVal :: Type -> Expr
theVal t = singleArgClo t "the_v" thePrim theLPrim

thePrim :: Expr -> Expr
thePrim e1 = let t1@(ListT t1') = typeOf e1
              in F.PApp1 t1' (F.FThe $ t1 .-> t1') e1

theLPrim :: Expr -> Expr
theLPrim e1 = let t1@(ListT t@(ListT _)) = typeOf e1
               in F.PApp1 t (F.FTheL $ t1 .-> t) e1

lastVal :: Type -> Expr
lastVal t = singleArgClo t "last_v" lastPrim lastLPrim

lastPrim :: Expr -> Expr
lastPrim e1 = let t1@(ListT t1') = typeOf e1
               in F.PApp1 t1' (F.FLast $ t1 .-> t1') e1

lastLPrim :: Expr -> Expr
lastLPrim e1 = let t1@(ListT t@(ListT _)) = typeOf e1
                in F.PApp1 t (F.FLastL $ t1 .-> t) e1


tailVal :: Type -> Expr
tailVal t = singleArgClo t "tail_v" tailPrim tailLPrim

tailPrim :: Expr -> Expr
tailPrim e1 = let t1@(ListT _) = typeOf e1
               in F.PApp1 t1 (F.FTail $ t1 .-> t1) e1

tailLPrim :: Expr -> Expr
tailLPrim e1 = let t1@(ListT (ListT _)) = typeOf e1
                in F.PApp1 t1 (F.FTailL $ t1 .-> t1) e1

nubVal :: Type -> Expr
nubVal t = singleArgClo t "nub_v" nubPrim nubLPrim

nubPrim :: Expr -> Expr
nubPrim e1 = let t1@(ListT _) = typeOf e1
               in F.PApp1 t1 (F.FNub $ t1 .-> t1) e1

nubLPrim :: Expr -> Expr
nubLPrim e1 = let t1@(ListT (ListT _)) = typeOf e1
                in F.PApp1 t1 (F.FNubL $ t1 .-> t1) e1

numberVal :: Type -> Expr
numberVal t = singleArgClo t "number_v" numberPrim numberLPrim

numberPrim :: Expr -> Expr
numberPrim e1 = let (ListT t) = typeOf e1
                in F.PApp1 (ListT (PairT t IntT )) (F.FNumber $ (ListT t) .-> (ListT (PairT t IntT ))) e1

numberLPrim :: Expr -> Expr
numberLPrim e1 = let t1@(ListT (ListT t)) = typeOf e1
                     rt = ListT (ListT (PairT t IntT))
                 in F.PApp1 rt (F.FNumberL $ t1 .-> rt) e1

initVal :: Type -> Expr
initVal t = singleArgClo t "init_v" initPrim initLPrim

initPrim :: Expr -> Expr
initPrim e1 = let t1@(ListT _) = typeOf e1
               in F.PApp1 t1 (F.FInit $ t1 .-> t1) e1

initLPrim :: Expr -> Expr
initLPrim e1 = let t1@(ListT (ListT _)) = typeOf e1
                in F.PApp1 t1 (F.FInitL $ t1 .-> t1) e1

reverseVal :: Type -> Expr
reverseVal t = singleArgClo t "reverse_v" reversePrim reverseLPrim

reversePrim :: Expr -> Expr
reversePrim e1 = let t1@(ListT _) = typeOf e1
               in F.PApp1 t1 (F.FReverse $ t1 .-> t1) e1

reverseLPrim :: Expr -> Expr
reverseLPrim e1 = let t1@(ListT (ListT _)) = typeOf e1
                in F.PApp1 t1 (F.FReverseL $ t1 .-> t1) e1

andVal :: Type -> Expr
andVal t = singleArgClo t "and_v" andPrim andLPrim

andPrim :: Expr -> Expr
andPrim e1 = let t1@(ListT BoolT) = typeOf e1
             in F.PApp1 BoolT (F.FAnd $ t1 .-> BoolT) e1

andLPrim :: Expr -> Expr 
andLPrim e1 = let t1@(ListT t@(ListT BoolT)) = typeOf e1
              in F.PApp1 t (F.FAndL $ t1 .-> t) e1


orVal :: Type -> Expr
orVal t = singleArgClo t "or_v" orPrim orLPrim

orPrim :: Expr -> Expr
orPrim e1 = let t1@(ListT BoolT) = typeOf e1
           in F.PApp1 BoolT (F.FOr $ t1 .-> BoolT) e1

orLPrim :: Expr -> Expr 
orLPrim e1 = let t1@(ListT t@(ListT BoolT)) = typeOf e1
            in F.PApp1 t (F.FOrL $ t1 .-> t) e1

sumVal :: Type -> Expr
sumVal t = singleArgClo t "sum_v" sumPrim sumLPrim

avgVal :: Type -> Expr
avgVal t = singleArgClo t "avg_v" avgPrim avgLPrim

sumPrim :: Expr -> Expr
sumPrim e1 = let t1@(ListT t) = typeOf e1
              in F.PApp1 t (F.FSum $ t1 .-> t) e1
              
avgPrim :: Expr -> Expr
avgPrim e1 = let t1 = typeOf e1
             in F.PApp1 DoubleT (F.FAvg $ t1 .-> DoubleT) e1

sumLPrim :: Expr -> Expr
sumLPrim e1 = let t1@(ListT t@(ListT _)) = typeOf e1
               in F.PApp1 t (F.FSumL $ t1 .-> t) e1
               
avgLPrim :: Expr -> Expr
avgLPrim e1 = let t1@(ListT _) = typeOf e1
              in F.PApp1 (ListT DoubleT) (F.FAvgL $ t1 .-> (ListT DoubleT)) e1

minimumVal :: Type -> Expr
minimumVal t = singleArgClo t "minimum_v" minimumPrim minimumLPrim

minimumPrim :: Expr -> Expr
minimumPrim e1 = let t1@(ListT t) = typeOf e1
                  in F.PApp1 t (F.FMinimum $ t1 .-> t) e1

minimumLPrim :: Expr -> Expr
minimumLPrim e1 = let t1@(ListT t@(ListT _)) = typeOf e1
                   in F.PApp1 t (F.FMinimumL $ t1 .-> t) e1

maximumVal :: Type -> Expr
maximumVal t = singleArgClo t "maximum_v" maximumPrim maximumLPrim

maximumPrim :: Expr -> Expr
maximumPrim e1 = let t1@(ListT t) = typeOf e1
                 in F.PApp1 t (F.FMaximum $ t1 .-> t) e1

maximumLPrim :: Expr -> Expr
maximumLPrim e1 = let t1@(ListT t@(ListT _)) = typeOf e1
                  in F.PApp1 t (F.FMaximumL $ t1 .-> t) e1


concatVal :: Type -> Expr
concatVal t = singleArgClo t "concat_v" concatPrim concatLPrim

qConcatPrim :: Expr -> Expr
qConcatPrim e = let t1@(ListT rt@(ListT _)) = typeOf e
                    ft = t1 .-> rt
                 in F.PApp1 rt (F.FQuickConcat ft) e

concatPrim :: Expr -> Expr
concatPrim e = let t1@(ListT rt@(ListT _)) = typeOf e
                   ft = t1 .-> rt
                in F.PApp1 rt (F.FConcat ft) e
                
concatLPrim :: Expr -> Expr
concatLPrim e = let t1@(ListT rt@(ListT (ListT _))) = typeOf e
                    ft = t1 .-> rt
                 in F.PApp1 rt (F.FConcatL $ ft) e

fstVal :: Type -> Expr
fstVal t = singleArgClo t "fst_v" fstPrim fstLPrim
        
sndVal :: Type -> Expr
sndVal t = singleArgClo t "snd_v" sndPrim sndLPrim

cloApp :: Expr -> Expr -> Expr
cloApp e1 ea = CloApp rt e1 ea
   where
       fty = typeOf e1
       (_, rt) = splitType fty
       
cloAppM :: Monad m => m Expr -> m Expr -> m Expr
cloAppM = liftM2 cloApp
                

cloLApp :: Expr -> Expr -> Expr
cloLApp e1 ea = CloLApp (liftType rt) e1 ea
    where
        fty = typeOf e1
        (_, rt) = splitType $ unliftType fty
        
cloLAppM :: Monad m => m Expr -> m Expr -> m Expr
cloLAppM = liftM2 cloLApp

distPrim :: Expr -> Expr -> Expr
distPrim e1 e2 = let t1 = typeOf e1
                     t2 = typeOf e2
                     ft = t1 .-> t2 .-> listT t1
                  in F.PApp2 (listT t1) (F.FDist ft) e1 e2

distLPrim :: Expr -> Expr -> Expr
distLPrim e1 e2 = let t1 = typeOf e1
                      t2 = typeOf e2
                      ft = t1 .-> t2 .-> listT t1
                   in F.PApp2 (listT t1) (F.FDistL ft) e1 e2

restrictPrim :: Expr -> Expr -> Expr
restrictPrim e1 e2 = let t1 = typeOf e1
                         rt = t1
                         ft = t1 .-> listT boolT .-> rt
                      in F.PApp2 rt (F.FRestrict ft) e1 e2

combinePrim :: Expr -> Expr -> Expr -> Expr
combinePrim e1 e2 e3 = let t1 = typeOf e1 
                           t2 = typeOf e2
                           rt = t2
                           ft = t1 .-> t2 .-> t2 .-> rt
                        in F.PApp3 rt (F.FCombine ft) e1 e2 e3


unconcatPrim :: Expr -> Expr -> Expr
unconcatPrim e1 e2 = let t1 = typeOf e1
                         t2 = typeOf e2
                         rt = listT t2
                         ft = t1 .-> t2 .-> rt
                      in F.PApp2 rt (F.FUnconcat ft) e1 e2 

intF :: Int -> Expr
intF i = F.Const intT $ IntV i

varF :: Type -> String -> Expr
varF t x = F.Var t x

fstPrim :: Expr -> Expr
fstPrim e = let t = typeOf e
             in case t of
                 (PairT t1 _) -> PApp1 t1 (F.FFst $ typeOf e .-> t1) e
                 _              -> error $ "fstPrim: Provided type is not a tuple: " ++ show t

sndPrim :: Expr -> Expr
sndPrim e = let t = typeOf e
             in case t of
                 (PairT _ t2) -> PApp1 t2 (F.FSnd $ typeOf e .-> t2) e
                 _             -> error $ "sndPrim: Provided type is not a tuple: " ++ show t

fstLPrim :: Expr -> Expr
fstLPrim e = let t = typeOf e
              in case t of
                  (ListT (PairT t1 _)) -> PApp1 (ListT t1) (F.FFstL $ t .-> ListT t1) e
                  _              -> error $ "fstLPrim: Provided type is not a tuple: " ++ show t

sndLPrim :: Expr -> Expr
sndLPrim e = let t = typeOf e
              in case t of
                  (ListT (PairT _ t2)) -> PApp1 (ListT t2) (F.FSndL $ t .-> ListT t2) e
                  _             -> error $ "sndLPrim: Provided type is not a tuple: "++ show t
\end{code}

%if False
\begin{code}
ifPrim :: Expr -> Expr -> Expr -> Expr
ifPrim eb et ee = let (tb, tt, te) = (typeOf eb, typeOf et, typeOf ee)
                   in if tb == boolT && tt == te
                       then If tt eb et ee
                       else error $ "ifPrim: Provided types are not compatible: " ++ pp tb ++ " " ++ show tt ++ " " ++ show te

ifPrimM :: Monad m => m Expr -> m Expr -> m Expr -> m Expr
ifPrimM = liftM3 ifPrim
    
binPrim :: Type -> ScalarBinOp -> Expr -> Expr -> Expr     
binPrim t o e1 e2 = 
    let t' = typeOf e1
    in case (t', o) of
           (PairT _ _, SBRelOp Eq) -> 
               binPrim t (SBBoolOp Conj) (binPrim t (SBRelOp Eq) (fstPrim e1) (fstPrim e2)) 
                                         (binPrim t (SBRelOp Eq) (sndPrim e1) (sndPrim e2))
           _                       -> BinOp t (NotLifted o) e1 e2

binPrimM :: Monad m => Type -> ScalarBinOp -> m Expr -> m Expr -> m Expr
binPrimM t o = liftM2 (binPrim t o)

binPrimL :: Type -> ScalarBinOp -> Expr -> Expr -> Expr
binPrimL t o = BinOp t (Lifted o) 

binPrimLM :: Monad m => Type -> ScalarBinOp -> m Expr -> m Expr -> m Expr
binPrimLM t o = liftM2 (binPrimL t o)

unPrim :: Type -> ScalarUnOp -> Expr -> Expr
unPrim t o e = UnOp t (NotLifted o) e

unPrimM :: Monad m => Type -> ScalarUnOp -> m Expr -> m Expr
unPrimM t o = liftM (unPrim t o)

unPrimL :: Type -> ScalarUnOp -> Expr -> Expr
unPrimL t o e = UnOp t (Lifted o) e

unPrimLM :: Monad m => Type -> ScalarUnOp -> m Expr -> m Expr
unPrimLM t o = liftM (unPrimL t o)

clo :: Type -> String -> [String] -> String -> Expr -> Expr -> Expr
clo = Clo

cloM :: Monad m => Type -> String -> [String] -> String -> m Expr -> m Expr -> m Expr
cloM t n fv a = liftM2 (Clo t n fv a)

cloL :: Type -> String -> [String] -> String -> Expr -> Expr -> Expr
cloL = AClo

cloLM :: Monad m => Type -> String -> [String] -> String -> m Expr -> m Expr -> m Expr
cloLM t n fv a = liftM2 (cloL t n fv a) 
\end{code}
%endif
