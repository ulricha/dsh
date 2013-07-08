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
module Database.DSH.FKL.FKLPrimitives where
       
import Database.DSH.FKL.Data.FKL as F
import Database.DSH.Common.Data.Val
import Database.DSH.Common.Data.Op
import Database.DSH.Common.Data.Type
import Database.DSH.Common.Data.JoinExpr

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

groupWithKeyVal :: Type -> Expr
groupWithKeyVal t = doubleArgClo t "group_f" "group_xs" groupWithKeyPrim groupWithKeyLPrim

groupWithKeyPrim :: Expr -> Expr -> Expr
groupWithKeyPrim f e = let arg1 = mapPrim f e
                           t1@(FunT _ tk) = typeOf arg1
                           t2           = typeOf e
                           t3           = listT $ pairT tk t2
                       in F.PApp2 t3 (F.GroupWithKeyS (t1 .-> t2 .-> t3)) arg1 e

groupWithKeyLPrim :: Expr -> Expr -> Expr
groupWithKeyLPrim f e = let arg1 = mapLPrim f e
                            t1@(FunT _ tk) = typeOf arg1 
                            t2           = typeOf e
                            t3           = listT $ pairT tk t2
                        in F.PApp2 t3 (F.GroupWithKeyL (t1 .-> t2 .-> t3)) arg1 e 

takeWithVal :: Type -> Expr
takeWithVal t = doubleArgClo t "take_f" "take_xs" takeWithPrim takeWithLPrim

takeWithPrim :: Expr -> Expr -> Expr
takeWithPrim f e = let arg1 = mapPrim f e
                       t1 = typeOf arg1
                       t2 = typeOf e
                    in F.PApp2 t2 (F.TakeWithS (t1 .-> t2 .-> t2)) arg1 e

takeWithLPrim :: Expr -> Expr -> Expr
takeWithLPrim f e = let arg1 = mapLPrim f e
                        t1 = typeOf arg1 
                        t2 = typeOf e
                     in F.PApp2 t2 (F.TakeWithL (t1 .-> t2 .-> t2)) arg1 e

dropWithVal :: Type -> Expr
dropWithVal t = doubleArgClo t "drop_f" "drop_xs" dropWithPrim dropWithLPrim

dropWithPrim :: Expr -> Expr -> Expr
dropWithPrim f e = let arg1 = mapPrim f e
                       t1 = typeOf arg1
                       t2 = typeOf e
                    in F.PApp2 t2 (F.DropWithS (t1 .-> t2 .-> t2)) arg1 e

dropWithLPrim :: Expr -> Expr -> Expr
dropWithLPrim f e = let arg1 = mapLPrim f e
                        t1 = typeOf arg1 
                        t2 = typeOf e
                     in F.PApp2 t2 (F.DropWithL (t1 .-> t2 .-> t2)) arg1 e

pairVal :: Type -> Expr
pairVal t = doubleArgClo t "pair_e1" "pair_e2" pairPrim pairLPrim

pairPrim :: Expr -> Expr -> Expr
pairPrim e1 e2 = let t1 = typeOf e1
                     t2 = typeOf e2
                     rt = pairT t1 t2
                  in F.PApp2 rt (F.Pair (t1 .-> t2 .-> rt)) e1 e2

pairLPrim :: Expr -> Expr -> Expr
pairLPrim e1 e2 = let t1@(ListT t1') = typeOf e1
                      t2@(ListT t2') = typeOf e2
                      rt = listT (pairT t1' t2')
                   in F.PApp2 rt (F.PairL (t1 .-> t2 .-> rt)) e1 e2 

takeVal :: Type -> Expr
takeVal t = doubleArgClo t "take_e1" "take_e2" takePrim takeLPrim

takePrim :: Expr -> Expr -> Expr
takePrim e1 e2 = let t1 = typeOf e1
                     t2 = typeOf e2
                  in F.PApp2 t2 (F.Take (t1 .-> t2 .-> t2)) e1 e2

takeLPrim :: Expr -> Expr -> Expr
takeLPrim e1 e2 = let t1 = typeOf e1
                      t2 = typeOf e2
                   in F.PApp2 t2 (F.TakeL (t1 .-> t2 .-> t2)) e1 e2

dropVal :: Type -> Expr
dropVal t = doubleArgClo t "drop_e1" "drop_e2" dropPrim dropLPrim

dropPrim :: Expr -> Expr -> Expr
dropPrim e1 e2 = let t1 = typeOf e1
                     t2 = typeOf e2
                  in F.PApp2 t2 (F.Drop (t1 .-> t2 .-> t2)) e1 e2

dropLPrim :: Expr -> Expr -> Expr
dropLPrim e1 e2 = let t1 = typeOf e1
                      t2 = typeOf e2
                   in F.PApp2 t2 (F.DropL (t1 .-> t2 .-> t2)) e1 e2

zipVal :: Type -> Expr
zipVal t = doubleArgClo t "zip_e1" "zip_e2" zipPrim zipLPrim

zipPrim :: Expr -> Expr -> Expr
zipPrim e1 e2 = let t1 = typeOf e1
                    t2 = typeOf e2
                 in F.PApp2 t2 (F.Zip (t1 .-> t2 .-> PairT t1 t2)) e1 e2

zipLPrim :: Expr -> Expr -> Expr
zipLPrim e1 e2 = let t1@(ListT t1') = typeOf e1
                     t2@(ListT t2') = typeOf e2
                  in F.PApp2 t2 (F.ZipL (t1 .-> t2 .-> listT (PairT t1' t2'))) e1 e2
                  
cartProductVal :: Type -> Expr
cartProductVal t = doubleArgClo t "cartProduct_e1" "cartProduct_e2" cartProductPrim cartProductLPrim
                  
cartProductPrim :: Expr -> Expr -> Expr
cartProductPrim e1 e2 = let t1 = typeOf e1
                            t2 = typeOf e2
                         in F.PApp2 t2 (F.CartProduct (t1 .-> t2 .-> PairT t1 t2)) e1 e2
                         
cartProductLPrim :: Expr -> Expr -> Expr
cartProductLPrim e1 e2 = let t1@(ListT t1') = typeOf e1
                             t2@(ListT t2') = typeOf e2
                          in F.PApp2 t2 (F.CartProductL (t1 .-> t2 .-> listT (PairT t1' t2'))) e1 e2

equiJoinVal :: JoinExpr -> JoinExpr -> Type -> Expr
equiJoinVal je1 je2 t = doubleArgClo t "equiJoin_e1" "equiJoin_e2" (equiJoinPrim je1 je2) (equiJoinLPrim je1 je2)
                  
equiJoinPrim :: JoinExpr -> JoinExpr -> Expr -> Expr -> Expr
equiJoinPrim je1 je2 e1 e2 = let t1 = typeOf e1
                                 t2 = typeOf e2
                             in F.PApp2 t2 (F.EquiJoin je1 je2 (t1 .-> t2 .-> PairT t1 t2)) e1 e2
                         
equiJoinLPrim :: JoinExpr -> JoinExpr -> Expr -> Expr -> Expr
equiJoinLPrim je1 je2 e1 e2 = let t1@(ListT t1') = typeOf e1
                                  t2@(ListT t2') = typeOf e2
                              in F.PApp2 t2 (F.EquiJoinL je1 je2 (t1 .-> t2 .-> listT (PairT t1' t2'))) e1 e2

nestJoinVal :: JoinExpr -> JoinExpr -> Type -> Expr
nestJoinVal je1 je2 t = doubleArgClo t "nestJoin_e1" "nestJoin_e2" (nestJoinPrim je1 je2) (nestJoinLPrim je1 je2)
                  
nestJoinPrim :: JoinExpr -> JoinExpr -> Expr -> Expr -> Expr
nestJoinPrim je1 je2 e1 e2 = let xst@(ListT xt) = typeOf e1
                                 yst@(ListT yt) = typeOf e2
                                 tr = listT $ pairT xt (listT yt)
                             in F.PApp2 tr (F.NestJoin je1 je2 (xst .-> yst .-> tr)) e1 e2
                         
nestJoinLPrim :: JoinExpr -> JoinExpr -> Expr -> Expr -> Expr
nestJoinLPrim je1 je2 e1 e2 = let xst@(ListT (ListT xt)) = typeOf e1
                                  yst@(ListT yt) = typeOf e2
                                  tr = listT $ listT $ pairT xt yt
                              in F.PApp2 tr (F.NestJoinL je1 je2 (xst .-> yst .-> tr)) e1 e2

semiJoinVal :: JoinExpr -> JoinExpr -> Type -> Expr
semiJoinVal je1 je2 t = doubleArgClo t "semiJoin_e1" "semiJoin_e2" (semiJoinPrim je1 je2) (semiJoinLPrim je1 je2)
                  
semiJoinPrim :: JoinExpr -> JoinExpr -> Expr -> Expr -> Expr
semiJoinPrim je1 je2 e1 e2 = let t1 = typeOf e1
                                 t2 = typeOf e2
                             in F.PApp2 t2 (F.SemiJoin je1 je2 (t1 .-> t2 .-> t1)) e1 e2
                         
semiJoinLPrim :: JoinExpr -> JoinExpr -> Expr -> Expr -> Expr
semiJoinLPrim je1 je2 e1 e2 = let t1 = typeOf e1
                                  t2 = typeOf e2
                              in F.PApp2 t2 (F.SemiJoinL je1 je2 (t1 .-> t2 .-> t1)) e1 e2

appendVal :: Type -> Expr
appendVal t = doubleArgClo t "append_e1" "append_e2" appendPrim appendLPrim

appendPrim :: Expr -> Expr -> Expr
appendPrim e1 e2 = let t1 = typeOf e1
                       t2 = typeOf e2
                 in F.PApp2 t1 (F.Append (t1 .-> t2 .-> t1)) e1 e2

appendLPrim :: Expr -> Expr -> Expr
appendLPrim e1 e2 = let t1@(ListT _) = typeOf e1
                        t2@(ListT _) = typeOf e2
                  in F.PApp2 t1 (F.AppendL (t1 .-> t2 .-> t1)) e1 e2 


indexVal :: Type -> Expr
indexVal t = doubleArgClo t "index_e1" "index_e2" indexPrim indexLPrim

indexPrim :: Expr -> Expr -> Expr
indexPrim e1 e2 = let t1@(ListT t) = typeOf e1
                      t2 = typeOf e2
                   in F.PApp2 t (F.Index (t1 .-> t2 .-> t)) e1 e2

indexLPrim :: Expr -> Expr -> Expr
indexLPrim e1 e2 = let t1@(ListT t) = typeOf e1
                       t2@(ListT _) = typeOf e2
                    in F.PApp2 t (F.IndexL (t1 .-> t2 .-> t)) e1 e2

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
                    in F.PApp2 t2 (F.SortWithS (t1 .-> t2 .-> t2)) arg1 e

sortWithLPrim :: Expr -> Expr -> Expr
sortWithLPrim f e = let arg1 = mapLPrim f e
                        t1@(ListT (ListT _)) = typeOf arg1 
                        t2@(ListT (ListT _)) = typeOf e
                     in F.PApp2 t2 (F.SortWithL (t1 .-> t2 .-> t2)) arg1 e

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
                 in F.PApp1 intT (F.LengthPrim $ t1 .-> intT) e1

lengthLPrim :: Expr -> Expr
lengthLPrim e1 = let t1@(ListT (ListT _)) = typeOf e1
                  in F.PApp1 (listT intT) (F.LengthLift $ t1 .-> listT intT) e1
    
headVal :: Type -> Expr
headVal = theVal

theVal :: Type -> Expr
theVal t = singleArgClo t "the_v" thePrim theLPrim

thePrim :: Expr -> Expr
thePrim e1 = let t1@(ListT t1') = typeOf e1
              in F.PApp1 t1' (F.The $ t1 .-> t1') e1

theLPrim :: Expr -> Expr
theLPrim e1 = let t1@(ListT t@(ListT _)) = typeOf e1
               in F.PApp1 t (F.TheL $ t1 .-> t) e1

lastVal :: Type -> Expr
lastVal t = singleArgClo t "last_v" lastPrim lastLPrim

lastPrim :: Expr -> Expr
lastPrim e1 = let t1@(ListT t1') = typeOf e1
               in F.PApp1 t1' (F.Last $ t1 .-> t1') e1

lastLPrim :: Expr -> Expr
lastLPrim e1 = let t1@(ListT t@(ListT _)) = typeOf e1
                in F.PApp1 t (F.LastL $ t1 .-> t) e1


tailVal :: Type -> Expr
tailVal t = singleArgClo t "tail_v" tailPrim tailLPrim

tailPrim :: Expr -> Expr
tailPrim e1 = let t1@(ListT _) = typeOf e1
               in F.PApp1 t1 (F.Tail $ t1 .-> t1) e1

tailLPrim :: Expr -> Expr
tailLPrim e1 = let t1@(ListT (ListT _)) = typeOf e1
                in F.PApp1 t1 (F.TailL $ t1 .-> t1) e1

nubVal :: Type -> Expr
nubVal t = singleArgClo t "nub_v" nubPrim nubLPrim

nubPrim :: Expr -> Expr
nubPrim e1 = let t1@(ListT _) = typeOf e1
               in F.PApp1 t1 (F.Nub $ t1 .-> t1) e1

nubLPrim :: Expr -> Expr
nubLPrim e1 = let t1@(ListT (ListT _)) = typeOf e1
                in F.PApp1 t1 (F.NubL $ t1 .-> t1) e1

numberVal :: Type -> Expr
numberVal t = singleArgClo t "number_v" numberPrim numberLPrim

numberPrim :: Expr -> Expr
numberPrim e1 = let t1@(ListT _) = typeOf e1
               in F.PApp1 t1 (F.Number $ t1 .-> (ListT IntT)) e1

numberLPrim :: Expr -> Expr
numberLPrim e1 = let t1@(ListT (ListT _)) = typeOf e1
                in F.PApp1 t1 (F.NumberL $ t1 .-> (ListT IntT)) e1

initVal :: Type -> Expr
initVal t = singleArgClo t "init_v" initPrim initLPrim

initPrim :: Expr -> Expr
initPrim e1 = let t1@(ListT _) = typeOf e1
               in F.PApp1 t1 (F.Init $ t1 .-> t1) e1

initLPrim :: Expr -> Expr
initLPrim e1 = let t1@(ListT (ListT _)) = typeOf e1
                in F.PApp1 t1 (F.InitL $ t1 .-> t1) e1

reverseVal :: Type -> Expr
reverseVal t = singleArgClo t "reverse_v" reversePrim reverseLPrim

reversePrim :: Expr -> Expr
reversePrim e1 = let t1@(ListT _) = typeOf e1
               in F.PApp1 t1 (F.Reverse $ t1 .-> t1) e1

reverseLPrim :: Expr -> Expr
reverseLPrim e1 = let t1@(ListT (ListT _)) = typeOf e1
                in F.PApp1 t1 (F.ReverseL $ t1 .-> t1) e1

notVal :: Type -> Expr
notVal t = singleArgClo t "not_v" notPrim notLPrim

notPrim :: Expr -> Expr
notPrim e1 = let t1@(BoolT) = typeOf e1
              in F.PApp1 t1 (F.NotPrim $ t1 .-> t1) e1
              
notLPrim :: Expr -> Expr 
notLPrim e1 = let t1@(ListT BoolT) = typeOf e1
               in F.PApp1 t1 (F.NotVec $ t1 .-> t1) e1

andVal :: Type -> Expr
andVal t = singleArgClo t "and_v" andPrim andLPrim

andPrim :: Expr -> Expr
andPrim e1 = let t1@(ListT BoolT) = typeOf e1
             in F.PApp1 BoolT (F.And $ t1 .-> BoolT) e1

andLPrim :: Expr -> Expr 
andLPrim e1 = let t1@(ListT t@(ListT BoolT)) = typeOf e1
              in F.PApp1 t (F.AndL $ t1 .-> t) e1


orVal :: Type -> Expr
orVal t = singleArgClo t "or_v" orPrim orLPrim

orPrim :: Expr -> Expr
orPrim e1 = let t1@(ListT BoolT) = typeOf e1
           in F.PApp1 BoolT (F.Or $ t1 .-> BoolT) e1

orLPrim :: Expr -> Expr 
orLPrim e1 = let t1@(ListT t@(ListT BoolT)) = typeOf e1
            in F.PApp1 t (F.OrL $ t1 .-> t) e1

integerToDoubleVal :: Type -> Expr
integerToDoubleVal t = singleArgClo t "integerToDouble_v" integerToDoublePrim integerToDoubleLPrim

integerToDoublePrim :: Expr -> Expr
integerToDoublePrim e1 = let t1@(IntT) = typeOf e1
                          in F.PApp1 DoubleT (F.IntegerToDouble $ t1 .-> DoubleT) e1

integerToDoubleLPrim :: Expr -> Expr 
integerToDoubleLPrim e1 = let t1@(ListT IntT) = typeOf e1
                          in F.PApp1 (ListT DoubleT) (F.IntegerToDoubleL $ t1 .-> ListT DoubleT) e1

sumVal :: Type -> Expr
sumVal t = singleArgClo t "sum_v" sumPrim sumLPrim

avgVal :: Type -> Expr
avgVal t = singleArgClo t "avg_v" avgPrim avgLPrim

sumPrim :: Expr -> Expr
sumPrim e1 = let t1@(ListT t) = typeOf e1
              in F.PApp1 t (F.Sum $ t1 .-> t) e1
              
avgPrim :: Expr -> Expr
avgPrim e1 = let t1 = typeOf e1
             in F.PApp1 DoubleT (F.Avg $ t1 .-> DoubleT) e1

sumLPrim :: Expr -> Expr
sumLPrim e1 = let t1@(ListT t@(ListT _)) = typeOf e1
               in F.PApp1 t (F.SumL $ t1 .-> t) e1
               
avgLPrim :: Expr -> Expr
avgLPrim e1 = let t1@(ListT _) = typeOf e1
              in F.PApp1 (ListT DoubleT) (F.AvgL $ t1 .-> (ListT DoubleT)) e1

minimumVal :: Type -> Expr
minimumVal t = singleArgClo t "minimum_v" minimumPrim minimumLPrim

minimumPrim :: Expr -> Expr
minimumPrim e1 = let t1@(ListT t) = typeOf e1
                  in F.PApp1 t (F.Minimum $ t1 .-> t) e1

minimumLPrim :: Expr -> Expr
minimumLPrim e1 = let t1@(ListT t@(ListT _)) = typeOf e1
                   in F.PApp1 t (F.MinimumL $ t1 .-> t) e1

maximumVal :: Type -> Expr
maximumVal t = singleArgClo t "maximum_v" maximumPrim maximumLPrim

maximumPrim :: Expr -> Expr
maximumPrim e1 = let t1@(ListT t) = typeOf e1
                 in F.PApp1 t (F.Maximum $ t1 .-> t) e1

maximumLPrim :: Expr -> Expr
maximumLPrim e1 = let t1@(ListT t@(ListT _)) = typeOf e1
                  in F.PApp1 t (F.MaximumL $ t1 .-> t) e1


concatVal :: Type -> Expr
concatVal t = singleArgClo t "concat_v" concatPrim concatLPrim

qConcatPrim :: Expr -> Expr
qConcatPrim e = let t1@(ListT rt@(ListT _)) = typeOf e
                    ft = t1 .-> rt
                 in F.PApp1 rt (F.QuickConcat ft) e

concatPrim :: Expr -> Expr
concatPrim e = let t1@(ListT rt@(ListT _)) = typeOf e
                   ft = t1 .-> rt
                in F.PApp1 rt (F.Concat ft) e
                
concatLPrim :: Expr -> Expr
concatLPrim e = let t1@(ListT rt@(ListT (ListT _))) = typeOf e
                    ft = t1 .-> rt
                 in F.PApp1 rt (F.ConcatLift $ ft) e

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
                  in F.PApp2 (listT t1) (F.Dist ft) e1 e2

distLPrim :: Expr -> Expr -> Expr
distLPrim e1 e2 = let t1 = typeOf e1
                      t2 = typeOf e2
                      ft = t1 .-> t2 .-> listT t1
                   in F.PApp2 (listT t1) (F.Dist_L ft) e1 e2

restrictPrim :: Expr -> Expr -> Expr
restrictPrim e1 e2 = let t1 = typeOf e1
                         rt = t1
                         ft = t1 .-> listT boolT .-> rt
                      in F.PApp2 rt (F.Restrict ft) e1 e2

combinePrim :: Expr -> Expr -> Expr -> Expr
combinePrim e1 e2 e3 = let t1 = typeOf e1 
                           t2 = typeOf e2
                           rt = t2
                           ft = t1 .-> t2 .-> t2 .-> rt
                        in F.PApp3 rt (F.Combine ft) e1 e2 e3


unconcatPrim :: Expr -> Expr -> Expr
unconcatPrim e1 e2 = let t1 = typeOf e1
                         t2 = typeOf e2
                         rt = listT t2
                         ft = t1 .-> t2 .-> rt
                      in F.PApp2 rt (F.Unconcat ft) e1 e2 

intF :: Int -> Expr
intF i = F.Const intT $ IntV i

varF :: Type -> String -> Expr
varF t x = F.Var t x

fstPrim :: Expr -> Expr
fstPrim e = let t = typeOf e
             in case t of
                 (PairT t1 _) -> PApp1 t1 (Fst $ typeOf e .-> t1) e
                 _              -> error $ "fstPrim: Provided type is not a tuple: " ++ show t

sndPrim :: Expr -> Expr
sndPrim e = let t = typeOf e
             in case t of
                 (PairT _ t2) -> PApp1 t2 (Snd $ typeOf e .-> t2) e
                 _             -> error $ "sndPrim: Provided type is not a tuple: " ++ show t

fstLPrim :: Expr -> Expr
fstLPrim e = let t = typeOf e
              in case t of
                  (ListT (PairT t1 _)) -> PApp1 (ListT t1) (FstL $ t .-> ListT t1) e
                  _              -> error $ "fstLPrim: Provided type is not a tuple: " ++ show t

sndLPrim :: Expr -> Expr
sndLPrim e = let t = typeOf e
              in case t of
                  (ListT (PairT _ t2)) -> PApp1 (ListT t2) (SndL $ t .-> ListT t2) e
                  _             -> error $ "sndLPrim: Provided type is not a tuple: "++ show t
\end{code}

%if False
\begin{code}
ifPrim :: Expr -> Expr -> Expr -> Expr
ifPrim eb et ee = let (tb, tt, te) = (typeOf eb, typeOf et, typeOf ee)
                   in if tb == boolT && tt == te
                       then If tt eb et ee
                       else error $ "ifPrim: Provided types are not compatible: " ++ show tb ++ " " ++ show tt ++ " " ++ show te

ifPrimM :: Monad m => m Expr -> m Expr -> m Expr -> m Expr
ifPrimM = liftM3 ifPrim
    
opPrim :: Type -> Oper -> Expr -> Expr -> Expr     
opPrim t o e1 e2 = let t' = typeOf e1
                    in case (t', o) of
                        (PairT _ _, Eq) -> opPrim t Conj (opPrim t Eq (fstPrim e1) (fstPrim e2)) (opPrim t Eq (sndPrim e1) (sndPrim e2))
                        _ -> BinOp t (Op o False) e1 e2

opPrimM :: Monad m => Type -> Oper -> m Expr -> m Expr -> m Expr
opPrimM t o = liftM2 (opPrim t o)

opPrimL :: Type -> Oper -> Expr -> Expr -> Expr
opPrimL t o = BinOp t (Op o True) 

opPrimLM :: Monad m => Type -> Oper -> m Expr -> m Expr -> m Expr
opPrimLM t o = liftM2 (opPrimL t o)

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
