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

-- tranposePrim :: [[a]] -> [[a]]
transposePrim :: Expr -> Expr
transposePrim e = 
    let t = typeOf e 
    in F.PApp1 t (F.Transpose (t .-> t)) e

-- transposeLPrim :: [[[a]]] -> [[[a]]]
transposeLPrim :: Expr -> Expr
transposeLPrim e = 
    let t = typeOf e
    in F.PApp1 t (F.TransposeL (t .-> t)) e

-- transpose :: [a] -> [[a]]
reshapePrim :: Integer -> Expr -> Expr
reshapePrim n e = 
    let t = typeOf e
    in F.PApp1 (ListT t) (F.Reshape n (t .-> ListT t)) e

-- transpose :: [[a]] -> [[[a]]]
reshapeLPrim :: Integer -> Expr -> Expr
reshapeLPrim n e = 
    let t = typeOf e
    in F.PApp1 (ListT t) (F.ReshapeL n (t .-> ListT t)) e

{-
groupWithKeyPrim :: Expr -> Expr -> Expr
groupWithKeyPrim f e = let arg1 = mapPrim f e
                           t1@(FunT _ tk) = typeOf arg1
                           t2           = typeOf e
                           t3           = listT $ pairT tk t2
                       in F.PApp2 t3 (F.GroupWithKey (t1 .-> t2 .-> t3)) arg1 e

groupWithKeyLPrim :: Expr -> Expr -> Expr
groupWithKeyLPrim f e = let arg1 = mapLPrim f e
                            t1@(FunT _ tk) = typeOf arg1 
                            t2           = typeOf e
                            t3           = listT $ pairT tk t2
                        in F.PApp2 t3 (F.GroupWithKeyL (t1 .-> t2 .-> t3)) arg1 e 
-}

consPrim :: Expr -> Expr -> Expr
consPrim e1 e2 = 
    let t1 = typeOf e1
        t2 = typeOf e2
    in F.PApp2 t2 (F.Cons (t1 .-> t2 .-> t2)) e1 e2

consLPrim :: Expr -> Expr -> Expr
consLPrim e1 e2 =
    let t1 = typeOf e1
        t2 = typeOf e2
    in F.PApp2 t2 (F.ConsL (t1 .-> t2 .-> t2)) e1 e2


pairPrim :: Expr -> Expr -> Expr
pairPrim e1 e2 = let t1 = typeOf e1
                     t2 = typeOf e2
                     rt = pairT t1 t2
                  in F.PApp2 rt (F.Pair (t1 .-> t2 .-> rt)) e1 e2

-- FIXME lifted pair is thetavalent to zip!
pairLPrim :: Expr -> Expr -> Expr
pairLPrim e1 e2 = let t1@(ListT t1') = typeOf e1
                      t2@(ListT t2') = typeOf e2
                      rt = listT (pairT t1' t2')
                   in F.PApp2 rt (F.PairL (t1 .-> t2 .-> rt)) e1 e2 

zipPrim :: Expr -> Expr -> Expr
zipPrim e1 e2 = let t1 = typeOf e1
                    t2 = typeOf e2
                 in F.PApp2 t2 (F.Zip (t1 .-> t2 .-> PairT t1 t2)) e1 e2

zipLPrim :: Expr -> Expr -> Expr
zipLPrim e1 e2 = let t1@(ListT t1') = typeOf e1
                     t2@(ListT t2') = typeOf e2
                  in F.PApp2 t2 (F.ZipL (t1 .-> t2 .-> listT (PairT t1' t2'))) e1 e2
                  
cartProductPrim :: Expr -> Expr -> Expr
cartProductPrim e1 e2 = let t1 = typeOf e1
                            t2 = typeOf e2
                         in F.PApp2 t2 (F.CartProduct (t1 .-> t2 .-> PairT t1 t2)) e1 e2
                         
cartProductLPrim :: Expr -> Expr -> Expr
cartProductLPrim e1 e2 = let t1@(ListT t1') = typeOf e1
                             t2@(ListT t2') = typeOf e2
                          in F.PApp2 t2 (F.CartProductL (t1 .-> t2 .-> listT (PairT t1' t2'))) e1 e2

nestProductPrim :: Expr -> Expr -> Expr
nestProductPrim e1 e2 = let t1 = typeOf e1
                            t2 = typeOf e2
                         -- [a] -> [b] -> [(a, [(a, b)])]
                         in F.PApp2 t2 (F.NestProduct (t1 .-> t2 .-> PairT t1 t2)) e1 e2
                         
nestProductLPrim :: Expr -> Expr -> Expr
nestProductLPrim e1 e2 = let t1@(ListT t1') = typeOf e1
                             t2@(ListT t2') = typeOf e2
                          in F.PApp2 t2 (F.NestProductL (t1 .-> t2 .-> listT (PairT t1' t2'))) e1 e2

thetaJoinPrim :: JoinPredicate JoinExpr  -> Expr -> Expr -> Expr
thetaJoinPrim p e1 e2 = let t1 = typeOf e1
                            t2 = typeOf e2
                        in F.PApp2 t2 (F.ThetaJoin p (t1 .-> t2 .-> PairT t1 t2)) e1 e2
                         
thetaJoinLPrim :: JoinPredicate JoinExpr  -> Expr -> Expr -> Expr
thetaJoinLPrim p e1 e2 = let t1@(ListT t1') = typeOf e1
                             t2@(ListT t2') = typeOf e2
                         in F.PApp2 t2 (F.ThetaJoinL p (t1 .-> t2 .-> listT (PairT t1' t2'))) e1 e2

nestJoinPrim :: JoinPredicate JoinExpr  -> Expr -> Expr -> Expr
nestJoinPrim p e1 e2 = let xst@(ListT xt) = typeOf e1
                           yst@(ListT yt) = typeOf e2
                           tr = listT $ pairT xt (listT yt)
                       in F.PApp2 tr (F.NestJoin p (xst .-> yst .-> tr)) e1 e2
                         
nestJoinLPrim :: JoinPredicate JoinExpr  -> Expr -> Expr -> Expr
nestJoinLPrim p e1 e2 = let xst@(ListT (ListT xt)) = typeOf e1
                            yst@(ListT yt) = typeOf e2
                            tr = listT $ listT $ pairT xt yt
                        in F.PApp2 tr (F.NestJoinL p (xst .-> yst .-> tr)) e1 e2

semiJoinPrim :: JoinPredicate JoinExpr  -> Expr -> Expr -> Expr
semiJoinPrim p e1 e2 = let t1 = typeOf e1
                           t2 = typeOf e2
                       in F.PApp2 t2 (F.SemiJoin p (t1 .-> t2 .-> t1)) e1 e2
                         
semiJoinLPrim :: JoinPredicate JoinExpr  -> Expr -> Expr -> Expr
semiJoinLPrim p e1 e2 = let t1 = typeOf e1
                            t2 = typeOf e2
                        in F.PApp2 t2 (F.SemiJoinL p (t1 .-> t2 .-> t1)) e1 e2

antiJoinPrim :: JoinPredicate JoinExpr  -> Expr -> Expr -> Expr
antiJoinPrim p e1 e2 = let t1 = typeOf e1
                           t2 = typeOf e2
                       in F.PApp2 t2 (F.AntiJoin p (t1 .-> t2 .-> t1)) e1 e2
                         
antiJoinLPrim :: JoinPredicate JoinExpr  -> Expr -> Expr -> Expr
antiJoinLPrim p e1 e2 = let t1 = typeOf e1
                            t2 = typeOf e2
                        in F.PApp2 t2 (F.AntiJoinL p (t1 .-> t2 .-> t1)) e1 e2

appendPrim :: Expr -> Expr -> Expr
appendPrim e1 e2 = let t1 = typeOf e1
                       t2 = typeOf e2
                 in F.PApp2 t1 (F.Append (t1 .-> t2 .-> t1)) e1 e2

appendLPrim :: Expr -> Expr -> Expr
appendLPrim e1 e2 = let t1@(ListT _) = typeOf e1
                        t2@(ListT _) = typeOf e2
                  in F.PApp2 t1 (F.AppendL (t1 .-> t2 .-> t1)) e1 e2 


indexPrim :: Expr -> Expr -> Expr
indexPrim e1 e2 = let t1@(ListT t) = typeOf e1
                      t2 = typeOf e2
                   in F.PApp2 t (F.Index (t1 .-> t2 .-> t)) e1 e2

indexLPrim :: Expr -> Expr -> Expr
indexLPrim e1 e2 = let t1@(ListT t) = typeOf e1
                       t2@(ListT _) = typeOf e2
                    in F.PApp2 t (F.IndexL (t1 .-> t2 .-> t)) e1 e2

{-
filterPrim :: Expr -> Expr -> Expr
filterPrim f e = let arg1 = mapPrim f e
                  in restrictPrim e arg1
-}
                  
{-
filterLPrim :: Expr -> Expr -> Expr
filterLPrim f e = let arg1 = qConcatPrim (mapLPrim f e)
                   in unconcatPrim e (restrictPrim (qConcatPrim e) arg1)
-}

--The sortWith combinator

{-
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
-}

lengthPrim :: Expr -> Expr
lengthPrim e1 = let t1@(ListT _) = typeOf e1
                 in F.PApp1 intT (F.Length $ t1 .-> intT) e1

lengthLPrim :: Expr -> Expr
lengthLPrim e1 = let t1@(ListT (ListT _)) = typeOf e1
                  in F.PApp1 (listT intT) (F.LengthL $ t1 .-> listT intT) e1
    
thePrim :: Expr -> Expr
thePrim e1 = let t1@(ListT t1') = typeOf e1
              in F.PApp1 t1' (F.The $ t1 .-> t1') e1

theLPrim :: Expr -> Expr
theLPrim e1 = let t1@(ListT t@(ListT _)) = typeOf e1
               in F.PApp1 t (F.TheL $ t1 .-> t) e1

lastPrim :: Expr -> Expr
lastPrim e1 = let t1@(ListT t1') = typeOf e1
               in F.PApp1 t1' (F.Last $ t1 .-> t1') e1

lastLPrim :: Expr -> Expr
lastLPrim e1 = let t1@(ListT t@(ListT _)) = typeOf e1
                in F.PApp1 t (F.LastL $ t1 .-> t) e1


tailPrim :: Expr -> Expr
tailPrim e1 = let t1@(ListT _) = typeOf e1
               in F.PApp1 t1 (F.Tail $ t1 .-> t1) e1

tailLPrim :: Expr -> Expr
tailLPrim e1 = let t1@(ListT (ListT _)) = typeOf e1
                in F.PApp1 t1 (F.TailL $ t1 .-> t1) e1

nubPrim :: Expr -> Expr
nubPrim e1 = let t1@(ListT _) = typeOf e1
               in F.PApp1 t1 (F.Nub $ t1 .-> t1) e1

nubLPrim :: Expr -> Expr
nubLPrim e1 = let t1@(ListT (ListT _)) = typeOf e1
                in F.PApp1 t1 (F.NubL $ t1 .-> t1) e1

numberPrim :: Expr -> Expr
numberPrim e1 = let (ListT t) = typeOf e1
                in F.PApp1 (ListT (PairT t IntT )) (F.Number $ (ListT t) .-> (ListT (PairT t IntT ))) e1

numberLPrim :: Expr -> Expr
numberLPrim e1 = let t1@(ListT (ListT t)) = typeOf e1
                     rt = ListT (ListT (PairT t IntT))
                 in F.PApp1 rt (F.NumberL $ t1 .-> rt) e1

initPrim :: Expr -> Expr
initPrim e1 = let t1@(ListT _) = typeOf e1
               in F.PApp1 t1 (F.Init $ t1 .-> t1) e1

initLPrim :: Expr -> Expr
initLPrim e1 = let t1@(ListT (ListT _)) = typeOf e1
                in F.PApp1 t1 (F.InitL $ t1 .-> t1) e1

reversePrim :: Expr -> Expr
reversePrim e1 = let t1@(ListT _) = typeOf e1
               in F.PApp1 t1 (F.Reverse $ t1 .-> t1) e1

reverseLPrim :: Expr -> Expr
reverseLPrim e1 = let t1@(ListT (ListT _)) = typeOf e1
                in F.PApp1 t1 (F.ReverseL $ t1 .-> t1) e1

andPrim :: Expr -> Expr
andPrim e1 = let t1@(ListT BoolT) = typeOf e1
             in F.PApp1 BoolT (F.And $ t1 .-> BoolT) e1

andLPrim :: Expr -> Expr 
andLPrim e1 = let t1@(ListT t@(ListT BoolT)) = typeOf e1
              in F.PApp1 t (F.AndL $ t1 .-> t) e1


orPrim :: Expr -> Expr
orPrim e1 = let t1@(ListT BoolT) = typeOf e1
           in F.PApp1 BoolT (F.Or $ t1 .-> BoolT) e1

orLPrim :: Expr -> Expr 
orLPrim e1 = let t1@(ListT t@(ListT BoolT)) = typeOf e1
            in F.PApp1 t (F.OrL $ t1 .-> t) e1

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

minimumPrim :: Expr -> Expr
minimumPrim e1 = let t1@(ListT t) = typeOf e1
                  in F.PApp1 t (F.Minimum $ t1 .-> t) e1

minimumLPrim :: Expr -> Expr
minimumLPrim e1 = let t1@(ListT t@(ListT _)) = typeOf e1
                   in F.PApp1 t (F.MinimumL $ t1 .-> t) e1

maximumPrim :: Expr -> Expr
maximumPrim e1 = let t1@(ListT t) = typeOf e1
                 in F.PApp1 t (F.Maximum $ t1 .-> t) e1

maximumLPrim :: Expr -> Expr
maximumLPrim e1 = let t1@(ListT t@(ListT _)) = typeOf e1
                  in F.PApp1 t (F.MaximumL $ t1 .-> t) e1


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
                 in F.PApp1 rt (F.ConcatL $ ft) e

distPrim :: Expr -> Expr -> Expr
distPrim e1 e2 = let t1 = typeOf e1
                     t2 = typeOf e2
                     ft = t1 .-> t2 .-> listT t1
                  in F.PApp2 (listT t1) (F.Dist ft) e1 e2

distLPrim :: Expr -> Expr -> Expr
distLPrim e1 e2 = let t1 = typeOf e1
                      t2 = typeOf e2
                      ft = t1 .-> t2 .-> listT t1
                   in F.PApp2 (listT t1) (F.DistL ft) e1 e2

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
                 (PairT t1 _) -> PApp1 t1 (F.Fst $ typeOf e .-> t1) e
                 _              -> error $ "fstPrim: Provided type is not a tuple: " ++ show t

sndPrim :: Expr -> Expr
sndPrim e = let t = typeOf e
             in case t of
                 (PairT _ t2) -> PApp1 t2 (F.Snd $ typeOf e .-> t2) e
                 _             -> error $ "sndPrim: Provided type is not a tuple: " ++ show t

fstLPrim :: Expr -> Expr
fstLPrim e = let t = typeOf e
              in case t of
                  (ListT (PairT t1 _)) -> PApp1 (ListT t1) (F.FstL $ t .-> ListT t1) e
                  _              -> error $ "fstLPrim: Provided type is not a tuple: " ++ show t

sndLPrim :: Expr -> Expr
sndLPrim e = let t = typeOf e
              in case t of
                  (ListT (PairT _ t2)) -> PApp1 (ListT t2) (F.SndL $ t .-> ListT t2) e
                  _             -> error $ "sndLPrim: Provided type is not a tuple: "++ show t

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

