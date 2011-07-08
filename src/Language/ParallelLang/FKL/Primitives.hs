{-
Module containing some primitive operations in AST form.

All of these are helper functions for the flattening transformation
-}
module Language.ParallelLang.FKL.Primitives where
    
import Language.ParallelLang.FKL.Data.FKL as F
import Language.ParallelLang.Common.Data.Val
import Language.ParallelLang.Common.Data.Type (intT, Typed(..), (.->), unliftTypeN, liftTypeN, boolT, listT, unliftType, splitType, liftType, Type(), tupleT)
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
        f2 = AClo (listT r1) [("n", F.Var (listT t1) "n"), ("__*group_f*", F.Var (listT t1) "__*group_f*")] "__*group_xs*" gws gwl

groupWithS :: Type -> TExpr -> TExpr -> TExpr
groupWithS t f e = F.App t (F.Var (typeOf f .-> typeOf e .-> t) "groupWithS") [mapS f e, e]

groupWithL :: Type -> TExpr -> TExpr -> TExpr
groupWithL t f e = F.App t (F.Var (typeOf f .-> typeOf e .-> t) "groupWithL") [mapL f e, e] 

-- The map combinators are used for desugaring iterators.
mapVal :: Type -> TExpr
mapVal t = Clo t "n" [] "__*map_f*" f1 f2
    where
        (t1, r1) = splitType t
        (t2, _r)  = splitType r1
        f1 = Clo r1 "n" [("__*map_f*", F.Var t1 "__*map_f*")] "__*map_xs*" (mapS (F.Var t1 "__*map_f*") (F.Var t2 "__*map_xs*")) (mapL (F.Var (listT t1) "__*map_f*") (F.Var (listT t2) "__*map_xs*")) 
        f2 = AClo (listT r1) [("n", F.Var (listT t1) "n"), ("__*map_f*", F.Var (listT t1) "__*map_f*")] "__*map_xs*" (mapS (F.Var t1 "__*map_f*") (F.Var t2 "__*map_xs*")) (mapL (F.Var (listT t1) "__*map_f*") (F.Var (listT t2) "__*map_xs*")) 

mapS :: TExpr -> TExpr -> TExpr
mapS f e = cloLApp (distF f e) e

mapL :: TExpr -> TExpr -> TExpr
mapL f e = unconcatF e $ cloLApp (concatF (distFL f e)) (concatF e)

lengthVal :: Type -> TExpr
lengthVal t = Clo t "n" [] "__*length_v*" f1 f2
    where
        (a, r) = splitType t
        f1 = F.App r (F.Var t "lengthPrim") [(F.Var a "__*length_v*")]
        f2 = F.App r (F.Var (liftType t) "lengthLift") [(F.Var (liftType a) "__*length_v*")]

notVal :: Type -> TExpr
notVal t = Clo t "n" [] "__*not_v*" f1 f2
    where
        (a, r) = splitType t
        f1 = F.App r (F.Var t "notPrim") [F.Var a "__*not_v*"]
        f2 = F.App r (F.Var (liftType t) "notVec") [F.Var (liftType a) "__*not_v*"]

concatVal :: Type -> TExpr
concatVal t = Clo t "n" [] "__*concat_v*" f1 f2
    where
        (a, r) = splitType t
        f1 = extractF (F.Var a "__*concat_v*") (F.Const intT (Int 1))
        f2 = F.App r (F.Var (liftType t) "concatLift") [F.Var (liftType a) "__*concat_v*"]

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
                in F.App t (F.Var (t1 .-> t2 .-> t) "index") [e1, e2]

distF :: TExpr -> TExpr -> TExpr
distF e1 e2 = let t1 = typeOf e1
                  t2 = typeOf e2
                  ft = t1 .-> t2 .-> listT t1
               in F.App (listT t1) (F.Var ft "dist") [e1, e2]

distFL :: TExpr -> TExpr -> TExpr
distFL e1 e2 = let t1 = typeOf e1
                   t2 = typeOf e2
                   ft = t1 .-> t2 .-> listT t1
                in F.App (listT t1) (F.Var ft "dist_L") [e1, e2]


lengthF :: TExpr -> TExpr
lengthF e1 = let t1 = typeOf e1
              in F.App intT (F.Var (t1 .-> intT) "length") [e1]

restrictF :: TExpr -> TExpr -> TExpr
restrictF e1 e2 = let t1 = typeOf e1
                      rt = t1
                      ft = t1 .-> listT boolT .-> rt
                   in F.App rt (F.Var ft "restrict") [e1, e2]

notF :: TExpr -> TExpr
notF e | typeOf e == boolT = F.App boolT (F.Var (boolT .-> boolT) "notPrim") [e]
       | typeOf e == listT boolT = F.App (listT boolT) (F.Var (listT boolT .-> listT boolT) "notVec") [e] 
       | otherwise = error $ "notF" ++ show (typeOf e)
       
combineF :: TExpr -> TExpr -> TExpr -> TExpr
combineF e1 e2 e3 = let t1 = typeOf e1 
                        t2 = typeOf e2
                        rt = t2
                        ft = t1 .-> t2 .-> t2 .-> rt
                     in F.App rt (F.Var ft "combine") [e1, e2, e3]


unconcatF :: TExpr -> TExpr -> TExpr
unconcatF e1 e2 = insertF e2 e1 (F.Const intT (Int 1))


insertF :: TExpr -> TExpr -> TExpr -> TExpr
insertF f v d@(F.Const _ (Int i)) = let t1 = typeOf f
                                        t2 = typeOf v
                                        rt = liftTypeN i t1
                                        ft = t1 .-> t2 .-> intT .-> rt
                                     in F.App rt (F.Var ft "insert") [f, v, d]
insertF _ _ _ = error "Third argument to insert should be an integer"


concatF :: TExpr -> TExpr
concatF e = extractF e (F.Const intT (Int 1))


extractF :: TExpr -> TExpr -> TExpr
extractF v d@(F.Const _ (Int i)) = let t1 = typeOf v
                                       rt = unliftTypeN i t1
                                       ft = t1 .-> intT .-> rt
                                    in F.App rt (F.Var ft "extract") [v, d]
extractF _ _ = error "Second argument to extract should be an integer"

bPermuteF :: TExpr -> TExpr -> TExpr
bPermuteF e1 e2 = F.App (typeOf e1) (F.Var (typeOf e1 .-> typeOf e2 .-> typeOf e1) "bPermute") [e1, e2] 

intF :: Int -> TExpr
intF i = F.Const intT $ Int i

varF :: Type -> String -> TExpr
varF t x = F.Var t x

zipF :: [TExpr] -> TExpr
zipF es = F.App resType (F.Var zipType $ "zip" ++ (show $ length es)) es
  where
     types = map typeOf es
     resType = (tupleT types)
     zipType = foldr (.->) resType types
     
letF :: String -> Expr t -> Expr t -> Expr t
letF v e1 e2 = F.Let (typeOf e2) v e1 e2

tagN :: String -> Expr t -> Expr t
tagN s e = Labeled s e

tupleF :: [TExpr] -> TExpr
tupleF es = F.App resType (F.Var tType tName) es
    where
        resType = tupleT [typeOf e | e <- es]
        tName = "(" ++ replicate ((length es) - 1) ',' ++ ")"
        tType = foldr (.->) resType (map typeOf es)

projectF :: TExpr -> Int -> TExpr
projectF e i = let t = typeOf e
                in case t of
                    (T.Tuple ts) -> if length ts >= i 
                                            then Proj (ts !! (i - 1)) 0 e i
                                            else error "Provided tuple expression is not big enough"
                    _                -> error "Provided type is not a tuple"            
