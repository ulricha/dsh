{-
Module containing some primitive operations in AST form.

All of these are helper functions for the flattening transformation
-}
module Language.ParallelLang.FKL.Primitives where
    
import Language.ParallelLang.FKL.Data.FKL as F
import Language.ParallelLang.Common.Data.Val
import Language.ParallelLang.Common.Data.Type (intT, Typed(..), (.->), unliftTypeN, liftTypeN, boolT, listT, unliftType, splitType, liftType, Type(), pairT)
import qualified Language.ParallelLang.Common.Data.Type as T

type TExpr = F.Expr Type

--The groupWith combinator

groupWithVal :: Type -> TExpr
groupWithVal t = Clo t "n" [] "__*group_f*" f1 f2
    where
        (t1, r1) = splitType t
        (t2, r) = splitType r1
        gws = groupWithS r (F.Var t1 "__*group_f*") (F.Var t2 "__*group_xs*")
        gwl = groupWithL (listT r) (F.Var (listT t1) "__*group_f*") (F.Var (listT t2) "__*group_xs*")
        f1 = Clo r1 "n" [("__*group_f*", F.Var t1 "__*group_f*")] "__*group_xs*" gws gwl
        f2 = AClo (listT r1) "n" (F.Var (listT t1) "n") [("__*group_f*", F.Var (listT t1) "__*group_f*")] "__*group_xs*" gws gwl

groupWithS :: Type -> TExpr -> TExpr -> TExpr
groupWithS t f e = F.PApp2 t (F.GroupWithS (typeOf f .-> typeOf e .-> t)) (mapS f e) e

groupWithL :: Type -> TExpr -> TExpr -> TExpr
groupWithL t f e = F.PApp2 t (F.GroupWithL (typeOf f .-> typeOf e .-> t)) (mapL f e) e 

--The sortWith combinator

sortWithVal :: Type -> TExpr
sortWithVal t = Clo t "n" [] "__*sort_f*" f1 f2
    where
        (t1, r1) = splitType t
        (t2, r) = splitType r1
        sws = sortWithS r (F.Var t1 "__*sort_f*") (F.Var t2 "__*sort_xs*")
        swl = sortWithL (listT r) (F.Var (listT t1) "__*sort_f*") (F.Var (listT t2) "__*sort_xs*")
        f1 = Clo r1 "n" [("__*sort_f*", F.Var t1 "__*sort_f*")] "__*sort_xs*" sws swl
        f2 = AClo (listT r1) "n" (F.Var (listT t1) "n") [("__*sort_f*", F.Var (listT t1) "__*sort_f*")] "__*sort_xs*" sws swl

sortWithS :: Type -> TExpr -> TExpr -> TExpr
sortWithS t f e = F.PApp2 t (F.SortWithS (typeOf f .-> typeOf e .-> t)) (mapS f e) e

sortWithL :: Type -> TExpr -> TExpr -> TExpr
sortWithL t f e = F.PApp2 t (F.SortWithL (typeOf f .-> typeOf e .-> t)) (mapL f e) e

-- The map combinators are used for desugaring iterators.
mapVal :: Type -> TExpr
mapVal t = Clo t "n" [] "__*map_f*" f1 f2
    where
        (t1, r1) = splitType t
        (t2, _r)  = splitType r1
        f1 = Clo r1 "n" [("__*map_f*", F.Var t1 "__*map_f*")] "__*map_xs*" (mapS (F.Var t1 "__*map_f*") (F.Var t2 "__*map_xs*")) (mapL (F.Var (listT t1) "__*map_f*") (F.Var (listT t2) "__*map_xs*")) 
        f2 = AClo (listT r1) "n" (F.Var (listT t1) "n") [("__*map_f*", F.Var (listT t1) "__*map_f*")] "__*map_xs*" (mapS (F.Var t1 "__*map_f*") (F.Var t2 "__*map_xs*")) (mapL (F.Var (listT t1) "__*map_f*") (F.Var (listT t2) "__*map_xs*")) 

mapS :: TExpr -> TExpr -> TExpr
mapS f e = cloLApp (distF f e) e

mapL :: TExpr -> TExpr -> TExpr
mapL f e = unconcatF e $ cloLApp (concatF (distFL f e)) (concatF e)

lengthVal :: Type -> TExpr
lengthVal t = Clo t "n" [] "__*length_v*" f1 f2
    where
        (a, r) = splitType t
        f1 = F.PApp1 r (F.LengthPrim t) (F.Var a "__*length_v*")
        f2 = F.PApp1 r (F.LengthLift (liftType t)) (F.Var (liftType a) "__*length_v*")

theVal :: Type -> TExpr
theVal t = Clo t "n" [] "__*the_v*" f1 f2
    where
        (a, r) = splitType t
        f1 = F.PApp1 r (F.The t) (F.Var a "__*the_v*")
        f2 = F.PApp1 r (F.TheL (liftType t)) (F.Var (liftType a) "__*the_v*")

notVal :: Type -> TExpr
notVal t = Clo t "n" [] "__*not_v*" f1 f2
    where
        (a, r) = splitType t
        f1 = F.PApp1 r (F.NotPrim t) $ F.Var a "__*not_v*"
        f2 = F.PApp1 r (F.NotVec (liftType t)) $ F.Var (liftType a) "__*not_v*"

sumVal :: Type -> TExpr
sumVal t = Clo t "n" [] "__*sum_v*" f1 f2
    where
        (a, r) = splitType t
        f1 = F.PApp1 r (F.Sum t) $ F.Var a "__*sum_v*"
        f2 = F.PApp1 r (F.SumL (liftType t)) $ F.Var (liftType a) "__*sum_v*"

concatVal :: Type -> TExpr
concatVal t = Clo t "n" [] "__*concat_v*" f1 f2
    where
        (a, r) = splitType t
        f1 = extractF (F.Var a "__*concat_v*") (F.Const intT (Int 1))
        f2 = F.PApp1 r (F.ConcatLift $ liftType t) $ F.Var (liftType a) "__*concat_v*"

cloApp :: TExpr -> TExpr -> TExpr
cloApp e1 ea = CloApp rt e1 ea
   where
       fty = typeOf e1
       (_, rt) = splitType fty

cloLApp :: TExpr -> TExpr -> TExpr
cloLApp e1 ea = CloLApp (liftType rt) e1 ea
    where
        fty = typeOf e1
        (_, rt) = splitType $ unliftType fty

indexF :: TExpr -> TExpr -> TExpr
indexF e1 e2 = let t1@(T.List t) = typeOf e1
                   t2 = typeOf e2
                in F.PApp2 t (F.Index $ t1 .-> t2 .-> t) e1 e2

distF :: TExpr -> TExpr -> TExpr
distF e1 e2 = let t1 = typeOf e1
                  t2 = typeOf e2
                  ft = t1 .-> t2 .-> listT t1
               in F.PApp2 (listT t1) (F.Dist ft) e1 e2

distFL :: TExpr -> TExpr -> TExpr
distFL e1 e2 = let t1 = typeOf e1
                   t2 = typeOf e2
                   ft = t1 .-> t2 .-> listT t1
                in F.PApp2 (listT t1) (F.Dist_L ft) e1 e2

{-
lengthF :: TExpr -> TExpr
lengthF e1 = let t1 = typeOf e1
              in F.PApp1 intT (F.Length $ t1 .-> intT) e1
-}

restrictF :: TExpr -> TExpr -> TExpr
restrictF e1 e2 = let t1 = typeOf e1
                      rt = t1
                      ft = t1 .-> listT boolT .-> rt
                   in F.PApp2 rt (F.Restrict ft) e1 e2

notF :: TExpr -> TExpr
notF e | typeOf e == boolT = F.PApp1 boolT (F.NotPrim $ boolT .-> boolT) e
       | typeOf e == listT boolT = F.PApp1 (listT boolT) (F.NotVec $ listT boolT .-> listT boolT) e 
       | otherwise = error $ "notF" ++ show (typeOf e)
       
combineF :: TExpr -> TExpr -> TExpr -> TExpr
combineF e1 e2 e3 = let t1 = typeOf e1 
                        t2 = typeOf e2
                        rt = t2
                        ft = t1 .-> t2 .-> t2 .-> rt
                     in F.PApp3 rt (F.Combine ft) e1 e2 e3


unconcatF :: TExpr -> TExpr -> TExpr
unconcatF e1 e2 = insertF e2 e1 (F.Const intT (Int 1))


insertF :: TExpr -> TExpr -> TExpr -> TExpr
insertF f v d@(F.Const _ (Int i)) = let t1 = typeOf f
                                        t2 = typeOf v
                                        rt = liftTypeN i t1
                                        ft = t1 .-> t2 .-> intT .-> rt
                                     in F.PApp3 rt (F.Insert ft) f v d
insertF _ _ _ = error "Third argument to insert should be an integer"


concatF :: TExpr -> TExpr
concatF e = extractF e (F.Const intT (Int 1))


extractF :: TExpr -> TExpr -> TExpr
extractF v d@(F.Const _ (Int i)) = let t1 = typeOf v
                                       rt = unliftTypeN i t1
                                       ft = t1 .-> intT .-> rt
                                    in F.PApp2 rt (F.Extract ft) v d
extractF _ _ = error "Second argument to extract should be an integer"

bPermuteF :: TExpr -> TExpr -> TExpr
bPermuteF e1 e2 = F.PApp2 (typeOf e1) (F.BPermute $ typeOf e1 .-> typeOf e2 .-> typeOf e1) e1 e2 

intF :: Int -> TExpr
intF i = F.Const intT $ Int i

varF :: Type -> String -> TExpr
varF t x = F.Var t x

letF :: String -> Expr t -> Expr t -> Expr t
letF v e1 e2 = F.Let (typeOf e2) v e1 e2

tagN :: String -> Expr t -> Expr t
tagN s e = Labeled s e


pairF :: TExpr -> TExpr -> TExpr
pairF e1 e2 = F.Pair (pairT (typeOf e1) (typeOf e2)) e1 e2


fstF :: TExpr -> TExpr
fstF e = let t = typeOf e
          in case t of
                (T.Pair t1 _) -> PApp1 t1 (Fst $ typeOf e .-> t1) e
                _              -> error "Provided type is not a tuple" 

sndF :: TExpr -> TExpr
sndF e = let t = typeOf e
          in case t of
                (T.Pair _ t2) -> PApp1 t2 (Snd $ typeOf e .-> t2) e
                _             -> error "Provided type is not a tuple"

fstLF :: TExpr -> TExpr
fstLF e = let t = typeOf e
          in case t of
                (T.List (T.Pair t1 _)) -> PApp1 (T.List t1) (Fst $ t .-> T.List t1) e
                _              -> error "Provided type is not a tuple" 

sndLF :: TExpr -> TExpr
sndLF e = let t = typeOf e
          in case t of
                (T.List (T.Pair _ t2)) -> PApp1 (T.List t2) (Snd $ t .-> T.List t2) e
                _             -> error "Provided type is not a tuple"
