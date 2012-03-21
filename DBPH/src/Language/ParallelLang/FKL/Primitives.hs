{-
Module containing some primitive operations in AST form.

All of these are helper functions for the flattening transformation
-}
module Language.ParallelLang.FKL.Primitives where
    
import Language.ParallelLang.FKL.Data.FKL as F
import Language.ParallelLang.Common.Data.Val
import Language.ParallelLang.Common.Data.Type (intT, Typed(..), (.->), boolT, listT, unliftType, splitType, liftType, Type(), pairT)
import qualified Language.ParallelLang.Common.Data.Type as T

--The groupWith combinator

groupWithVal :: Type -> Expr
groupWithVal t = Clo t "n" [] "__*group_f*" f1 f2
    where
        (t1, r1) = splitType t
        (t2, r) = splitType r1
        gws = groupWithS r (F.Var t1 "__*group_f*") (F.Var t2 "__*group_xs*")
        gwl = groupWithL (listT r) (F.Var (listT t1) "__*group_f*") (F.Var (listT t2) "__*group_xs*")
        f1 = Clo r1 "n" [("__*group_f*", F.Var t1 "__*group_f*")] "__*group_xs*" gws gwl
        f2 = AClo (listT r1) "n" (F.Var (listT t1) "n") [("__*group_f*", F.Var (listT t1) "__*group_f*")] "__*group_xs*" gws gwl

groupWithS :: Type -> Expr -> Expr -> Expr
groupWithS t f e = F.PApp2 t (F.GroupWithS (typeOf f .-> typeOf e .-> t)) (mapS f e) e

groupWithL :: Type -> Expr -> Expr -> Expr
groupWithL t f e = F.PApp2 t (F.GroupWithL (typeOf f .-> typeOf e .-> t)) (mapL f e) e 

--The sortWith combinator

sortWithVal :: Type -> Expr
sortWithVal t = Clo t "n" [] "__*sort_f*" f1 f2
    where
        (t1, r1) = splitType t
        (t2, r) = splitType r1
        sws = sortWithS r (F.Var t1 "__*sort_f*") (F.Var t2 "__*sort_xs*")
        swl = sortWithL (listT r) (F.Var (listT t1) "__*sort_f*") (F.Var (listT t2) "__*sort_xs*")
        f1 = Clo r1 "n" [("__*sort_f*", F.Var t1 "__*sort_f*")] "__*sort_xs*" sws swl
        f2 = AClo (listT r1) "n" (F.Var (listT t1) "n") [("__*sort_f*", F.Var (listT t1) "__*sort_f*")] "__*sort_xs*" sws swl

sortWithS :: Type -> Expr -> Expr -> Expr
sortWithS t f e = F.PApp2 t (F.SortWithS (typeOf f .-> typeOf e .-> t)) (mapS f e) e

sortWithL :: Type -> Expr -> Expr -> Expr
sortWithL t f e = F.PApp2 t (F.SortWithL (typeOf f .-> typeOf e .-> t)) (mapL f e) e

-- The map combinators are used for desugaring iterators.
mapVal :: Type -> Expr
mapVal t = Clo t "n" [] "__*map_f*" f1 f2
    where
        (t1, r1) = splitType t
        (t2, _r)  = splitType r1
        f1 = Clo r1 "n" [("__*map_f*", F.Var t1 "__*map_f*")] "__*map_xs*" (mapS (F.Var t1 "__*map_f*") (F.Var t2 "__*map_xs*")) (mapL (F.Var (listT t1) "__*map_f*") (F.Var (listT t2) "__*map_xs*")) 
        f2 = AClo (listT r1) "n" (F.Var (listT t1) "n") [("__*map_f*", F.Var (listT t1) "__*map_f*")] "__*map_xs*" (mapS (F.Var t1 "__*map_f*") (F.Var t2 "__*map_xs*")) (mapL (F.Var (listT t1) "__*map_f*") (F.Var (listT t2) "__*map_xs*")) 

mapS :: Expr -> Expr -> Expr
mapS f e = cloLApp (distF f e) e

mapL :: Expr -> Expr -> Expr
mapL f e = unconcatF e $ cloLApp (concatF (distFL f e)) (concatF e)

lengthVal :: Type -> Expr
lengthVal t = Clo t "n" [] "__*length_v*" f1 f2
    where
        (a, r) = splitType t
        f1 = F.PApp1 r (F.LengthPrim t) (F.Var a "__*length_v*")
        f2 = F.PApp1 r (F.LengthLift (liftType t)) (F.Var (liftType a) "__*length_v*")

theVal :: Type -> Expr
theVal t = Clo t "n" [] "__*the_v*" f1 f2
    where
        (a, r) = splitType t
        f1 = F.PApp1 r (F.The t) (F.Var a "__*the_v*")
        f2 = F.PApp1 r (F.TheL (liftType t)) (F.Var (liftType a) "__*the_v*")

notVal :: Type -> Expr
notVal t = Clo t "n" [] "__*not_v*" f1 f2
    where
        (a, r) = splitType t
        f1 = F.PApp1 r (F.NotPrim t) $ F.Var a "__*not_v*"
        f2 = F.PApp1 r (F.NotVec (liftType t)) $ F.Var (liftType a) "__*not_v*"

sumVal :: Type -> Expr
sumVal t = Clo t "n" [] "__*sum_v*" f1 f2
    where
        (a, r) = splitType t
        f1 = F.PApp1 r (F.Sum t) $ F.Var a "__*sum_v*"
        f2 = F.PApp1 r (F.SumL (liftType t)) $ F.Var (liftType a) "__*sum_v*"

concatVal :: Type -> Expr
concatVal t = Clo t "n" [] "__*concat_v*" f1 f2
    where
        (a, r) = splitType t
        f1 = concatF (F.Var a "__*concat_v*")
        f2 = F.PApp1 r (F.ConcatLift $ liftType t) $ F.Var (liftType a) "__*concat_v*"

fstVal :: Type -> Expr
fstVal t = Clo t "n" [] "__*fst_v*" f1 f2
    where
        (a, _) = splitType t
        f1 = fstF (F.Var a "__*fst_v*")
        f2 = fstLF (F.Var a "__*fst_v*")
        
sndVal :: Type -> Expr
sndVal t = Clo t "n" [] "__*snd_v*" f1 f2
    where
        (a, _) = splitType t
        f1 = sndF (F.Var a "__*snd_v*")
        f2 = sndLF (F.Var a "__*snd_v*")

cloApp :: Expr -> Expr -> Expr
cloApp e1 ea = CloApp rt e1 ea
   where
       fty = typeOf e1
       (_, rt) = splitType fty

cloLApp :: Expr -> Expr -> Expr
cloLApp e1 ea = CloLApp (liftType rt) e1 ea
    where
        fty = typeOf e1
        (_, rt) = splitType $ unliftType fty

indexF :: Expr -> Expr -> Expr
indexF e1 e2 = let t1@(T.List t) = typeOf e1
                   t2 = typeOf e2
                in F.PApp2 t (F.Index $ t1 .-> t2 .-> t) e1 e2

distF :: Expr -> Expr -> Expr
distF e1 e2 = let t1 = typeOf e1
                  t2 = typeOf e2
                  ft = t1 .-> t2 .-> listT t1
               in F.PApp2 (listT t1) (F.Dist ft) e1 e2

distFL :: Expr -> Expr -> Expr
distFL e1 e2 = let t1 = typeOf e1
                   t2 = typeOf e2
                   ft = t1 .-> t2 .-> listT t1
                in F.PApp2 (listT t1) (F.Dist_L ft) e1 e2

restrictF :: Expr -> Expr -> Expr
restrictF e1 e2 = let t1 = typeOf e1
                      rt = t1
                      ft = t1 .-> listT boolT .-> rt
                   in F.PApp2 rt (F.Restrict ft) e1 e2

notF :: Expr -> Expr
notF e | typeOf e == boolT = F.PApp1 boolT (F.NotPrim $ boolT .-> boolT) e
       | typeOf e == listT boolT = F.PApp1 (listT boolT) (F.NotVec $ listT boolT .-> listT boolT) e 
       | otherwise = error $ "notF" ++ show (typeOf e)
       
combineF :: Expr -> Expr -> Expr -> Expr
combineF e1 e2 e3 = let t1 = typeOf e1 
                        t2 = typeOf e2
                        rt = t2
                        ft = t1 .-> t2 .-> t2 .-> rt
                     in F.PApp3 rt (F.Combine ft) e1 e2 e3


unconcatF :: Expr -> Expr -> Expr
unconcatF e1 e2 = let t1 = typeOf e1
                      t2 = typeOf e2
                      rt = listT t2
                      ft = t1 .-> t2 .-> rt
                   in F.PApp2 rt (F.Unconcat ft) e1 e2 

concatF :: Expr -> Expr
concatF e = let t1@(T.List rt) = typeOf e
                ft = t1 .-> rt
             in F.PApp1 rt (F.Concat ft) e

bPermuteF :: Expr -> Expr -> Expr
bPermuteF e1 e2 = F.PApp2 (typeOf e1) (F.BPermute $ typeOf e1 .-> typeOf e2 .-> typeOf e1) e1 e2 

intF :: Int -> Expr
intF i = F.Const intT $ Int i

varF :: Type -> String -> Expr
varF t x = F.Var t x

letF :: String -> Expr -> Expr -> Expr
letF v e1 e2 = F.Let (typeOf e2) v e1 e2

tagN :: String -> Expr -> Expr
tagN s e = Labeled s e


pairF :: Expr -> Expr -> Expr
pairF e1 e2 = F.Pair (pairT (typeOf e1) (typeOf e2)) e1 e2


fstF :: Expr -> Expr
fstF e = let t = typeOf e
          in case t of
                (T.Pair t1 _) -> PApp1 t1 (Fst $ typeOf e .-> t1) e
                _              -> error "Provided type is not a tuple" 

sndF :: Expr -> Expr
sndF e = let t = typeOf e
          in case t of
                (T.Pair _ t2) -> PApp1 t2 (Snd $ typeOf e .-> t2) e
                _             -> error "Provided type is not a tuple"

fstLF :: Expr -> Expr
fstLF e = let t = typeOf e
          in case t of
                (T.List (T.Pair t1 _)) -> PApp1 (T.List t1) (Fst $ t .-> T.List t1) e
                _              -> error "Provided type is not a tuple" 

sndLF :: Expr -> Expr
sndLF e = let t = typeOf e
          in case t of
                (T.List (T.Pair _ t2)) -> PApp1 (T.List t2) (Snd $ t .-> T.List t2) e
                _             -> error "Provided type is not a tuple"
