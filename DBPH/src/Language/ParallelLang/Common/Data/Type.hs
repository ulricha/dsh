{-# LANGUAGE GADTs, TypeSynonymInstances, MultiParamTypeClasses #-}
module Language.ParallelLang.Common.Data.Type 
 (splitType, varsInType, listDepth, tupleT, extractTuple, containsTuple, tupleComponents, splitTypeArgsRes, extractFnRes, extractFnArgs, extractShape, unliftTypeN, unliftType, liftType, liftTypeN, Type(..), intT, boolT, unitT, stringT, doubleT, pairT, listT, Subst, Substitutable, (.->), apply, addSubstitution, Typed (..), funToCloTy)
where
    
import qualified Data.Map as M
import qualified Data.List as L
import qualified Data.Set as S

instance Show Type where 
    show (Var v) = v
    show (Fn t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
--    show (LFn t1 t2) = "(" ++ show t1 ++ " :-> " ++ show t2 ++ ")"
    show (TyC c []) = c
    show (TyC c ts) = case c of
                        "List"  -> "[" ++ (show $ head ts) ++ "]"
                        "tuple" -> "(" ++ (concat $ L.intersperse ", " (map show ts)) ++ ")"
                        _       -> c ++ (concat $ L.intersperse " " (map show ts)) 

data Type where
    Var :: String -> Type
    TyC :: String -> [Type] -> Type
    Fn :: Type -> Type -> Type
--    LFn :: Type -> Type -> Type
    deriving (Eq, Ord)

-- infixr 7 .~>
infixr 6 .->

infixr 7 .:->

varsInType :: Type -> [String]
varsInType (Fn t1 t2) = varsInType t1 ++ varsInType t2
-- varsInType (LFn t1 t2) = varsInType t1 ++ varsInType t2
varsInType (TyC _ vs) = concatMap varsInType vs
varsInType (Var v) = [v]

-- (.~>) :: Type -> Type -> Type
-- t1 .~> t2 = LFn t1 t2

(.:->) :: Type -> Type -> Type
t1 .:-> t2 = TyC ":->" [t1, t2]

(.->) :: Type -> Type -> Type
t1 .-> t2 = Fn t1 t2

intT :: Type
intT = TyC "Int" []

stringT :: Type
stringT = TyC "String" []

doubleT :: Type
doubleT = TyC "Double" []

boolT :: Type
boolT = TyC "Bool" []

unitT :: Type
unitT = TyC "()" []

pairT :: Type -> Type -> Type
pairT t1 t2 = TyC "tuple" [t1, t2]

tupleT :: [Type] -> Type
tupleT = TyC "tuple"

listT :: Type -> Type
listT t1 = TyC "List" [t1]

listDepth :: Type -> Int
listDepth (TyC "List" [t1]) = 1 + listDepth t1
listDepth _                 = 0

containsTuple :: Type -> Bool
containsTuple (Fn t1 t2) = containsTuple t1 || containsTuple t2
containsTuple (TyC "tuple" _) = True
containsTuple (TyC _ ts) = or $ map containsTuple ts
containsTuple _          = False

extractTuple :: Type -> (Type, Type -> Type, Int)
extractTuple (TyC "List" [t1]) = let (t, f, i) = extractTuple t1
                                  in (t, \x -> TyC "List" [f x], i + 1)
extractTuple t@(TyC "tuple" _) = (t, id, 0) 
extractTuple _                 = error "Type doesn't contain a tuple, cannot extract tuple"

tupleComponents :: Type -> [Type]
tupleComponents (TyC "tuple" ts) = ts
tupleComponents t   = error $ "Type is not a tuple type: " ++ show t

extractFnRes :: Type -> Type
extractFnRes = snd . splitTypeArgsRes

extractFnArgs :: Type -> [Type]
extractFnArgs = fst . splitTypeArgsRes

splitTypeArgsRes :: Type -> ([Type], Type)
splitTypeArgsRes (Fn t1 t2) = let (args, r) = splitTypeArgsRes t2 in (t1:args, r)
splitTypeArgsRes t          = ([], t)

splitType :: Type -> (Type, Type)
splitType (Fn t1 t2) = (t1, t2)
splitType _          = error "Can only split function types"

extractShape :: Type -> Type -> Type
extractShape (TyC "List" [t1]) = \x -> listT $ extractShape t1 x
extractShape _                 = \x -> x

liftTypeN :: Int -> Type -> Type
liftTypeN 0 t = t
liftTypeN i t = liftTypeN (i - 1) $ liftType t

liftType :: Type -> Type
liftType (Fn t1 t2) = Fn (liftType t1) (liftType t2)
liftType t = listT t 

unliftTypeN :: Int -> Type -> Type
unliftTypeN 0 t = t
unliftTypeN i t = unliftTypeN (i - 1) $ unliftType t

unliftType :: Type -> Type
unliftType (TyC "List" [t1]) = t1
unliftType t                 = error $ "Type: " ++ show t ++ " cannot be unlifted."


type Subst = M.Map String Type

class Substitutable a where
    apply :: Subst -> a -> a

instance Substitutable Type where
    apply s (Fn t1 t2) = Fn (apply s t1) (apply s t2)
--    apply s (LFn t1 t2) = LFn (apply s t1) (apply s t2)
    apply s (TyC n args) = TyC n $ map (apply s) args
    apply s t@(Var v2) = M.findWithDefault t v2 s

addSubstitution :: Subst -> String -> Type -> Subst
addSubstitution s i t = let s' = M.singleton i t
                            s'' = M.map (apply s') s
                         in s' `M.union` s''

funToCloTy :: Type -> Type
funToCloTy (Fn t1 t2) = t1 .:-> (funToCloTy t2)
funToCloTy t          = t 

class Typed a t where
  typeOf :: a t -> t
  freeVars :: [String] -> a t -> S.Set (String, a t)