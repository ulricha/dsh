{-# LANGUAGE GADTs, TypeSynonymInstances, MultiParamTypeClasses #-}
module Language.ParallelLang.Common.Data.Type 
 (varsInType, listDepth, tupleT, extractTuple, containsTuple, tupleComponents, unsafeInstantiate, splitTypeArgsRes, extractFnRes, extractFnArgs, extractShape, unliftTypeN, unliftType, liftType, liftTypeN, emptyTyEnv, TypeScheme(..), Type(..), intT, boolT, unitT, pairT, listT, Subst, Substitutable, (.->), apply, addSubstitution, TyEnv, generalise, Typed (..))
where
    
import qualified Data.Map as M
import qualified Data.List as L

type TyEnv = String -> TypeScheme

emptyTyEnv :: TyEnv
emptyTyEnv = \i -> error $ "Variable " ++ i ++ " not bound in env." 

instance Show TypeScheme where
    show (Forall v t) = "forall " ++ v ++ ". " ++ show t
    show (Ty t) = show t
    
instance Show Type where 
    show (Var v) = v
    show (Fn t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
    show (TyC c []) = c
    show (TyC c ts) = case c of
                        "List"  -> "[" ++ (show $ head ts) ++ "]"
                        "tuple" -> "(" ++ (concat $ L.intersperse ", " (map show ts)) ++ ")"
                        _       -> c ++ (concat $ L.intersperse " " (map show ts)) 

data TypeScheme where
    Forall :: String -> TypeScheme -> TypeScheme
    Ty :: Type -> TypeScheme

data Type where
    Var :: String -> Type
    TyC :: String -> [Type] -> Type
    Fn :: Type -> Type -> Type
    deriving Eq
--    Forall :: String -> Type -> Type

infixr 6 .->

varsInType :: Type -> [String]
varsInType (Fn t1 t2) = varsInType t1 ++ varsInType t2
varsInType (TyC _ vs) = concatMap varsInType vs
varsInType (Var v) = [v]

(.->) :: Type -> Type -> Type
t1 .-> t2 = Fn t1 t2

intT :: Type
intT = TyC "Int" []

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

{-
containsTuple :: Type -> Bool
containsTuple (TyC "List" [t1]) = containsTuple t1
containsTuple (TyC "tuple" _) = True
containsTuple _               = False
-}

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
    apply s (TyC n args) = TyC n $ map (apply s) args
    apply s t@(Var v2) = M.findWithDefault t v2 s

instance Substitutable TypeScheme where
    apply _ t@(Forall _ _) = t
    apply s (Ty t) = Ty $ apply s t

instance Substitutable TyEnv where
    apply s env = (\x -> apply s $ env x)
    
addSubstitution :: Subst -> String -> Type -> Subst
addSubstitution s i t = let s' = M.singleton i t
                            s'' = M.map (apply s') s
                         in s' `M.union` s''

generalise :: Type -> TypeScheme
generalise t = let fv = collectFreeVars t
                in foldr Forall (Ty t) fv
                
unsafeInstantiate :: TypeScheme -> Type
unsafeInstantiate (Forall _ t) = unsafeInstantiate t
unsafeInstantiate (Ty t)       = t

collectFreeVars :: Type -> [String]
collectFreeVars (Fn t1 t2) = L.nub $ (collectFreeVars t1 ++ collectFreeVars t2)
collectFreeVars (TyC _ ts) = L.nub $ concatMap collectFreeVars ts
collectFreeVars (Var t) = [t]

class Typed a t where
  typeOf :: a t -> t