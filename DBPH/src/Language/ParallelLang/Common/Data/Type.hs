{-# LANGUAGE GADTs, TypeSynonymInstances, MultiParamTypeClasses #-}
module Language.ParallelLang.Common.Data.Type 
 (transType, extractPair, splitType, varsInType, listDepth, pairT, containsTuple, pairComponents, splitTypeArgsRes, extractFnRes, extractFnArgs, extractShape, unliftTypeN, unliftType, liftType, liftTypeN, Type(..), intT, boolT, unitT, stringT, doubleT, listT, (.->), Typed (..), isFuns)
where
    
instance Show Type where 
    show (Var v) = v
    show (Fn t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
    show Int = "Int"
    show Nat = "Nat"
    show Bool = "Bool"
    show Double = "Double"
    show String = "String"
    show Unit = "()"
    show (List t) = "[" ++ (show t) ++ "]"
--    show (Tuple ts) = "(" ++ (concat $ L.intersperse ", " (map show ts)) ++ ")"
    show (Pair t1 t2) = "(" ++ show t1 ++ ", " ++ show t2 ++ ")"

data Type where
    Var :: String -> Type
    Fn :: Type -> Type -> Type
    Nat :: Type
    Int :: Type
    Bool :: Type
    Double :: Type
    String :: Type
    Unit :: Type
--    Tuple :: [Type] -> Type
    Pair :: Type -> Type -> Type
    List :: Type -> Type
    deriving (Eq, Ord)

infixr 6 .->

varsInType :: Type -> [String]
varsInType (Fn t1 t2) = varsInType t1 ++ varsInType t2
varsInType (Pair t1 t2) = varsInType t1 ++ varsInType t2
-- varsInType (Tuple vs) = concatMap varsInType vs
varsInType (List t) = varsInType t
varsInType (Var v) = [v]
varsInType _ = []

(.->) :: Type -> Type -> Type
t1 .-> t2 = Fn t1 t2

intT :: Type
intT = Int

stringT :: Type
stringT = String

doubleT :: Type
doubleT = Double

boolT :: Type
boolT = Bool

unitT :: Type
unitT = Unit

pairT :: Type -> Type -> Type
pairT t1 t2 = Pair t1 t2

{-
tupleT :: [Type] -> Type
tupleT = Tuple
-}

listT :: Type -> Type
listT = List

listDepth :: Type -> Int
listDepth (List t1) = 1 + listDepth t1
listDepth _                 = 0

containsTuple :: Type -> Bool
containsTuple (Fn t1 t2) = containsTuple t1 || containsTuple t2
-- containsTuple (Tuple _)  = True
containsTuple (Pair _ _)  = True
containsTuple (List t)   = containsTuple t
containsTuple _          = False

{-
extractTuple :: Type -> (Type, Type -> Type, Int)
extractTuple (List t1)   = let (t, f, i) = extractTuple t1
                            in (t, \x -> List (f x), i + 1)
extractTuple t@(Tuple _) = (t, id, 0) 
extractTuple _           = error "Type doesn't contain a tuple, cannot extract tuple"
-}

extractPair :: Type -> Type
extractPair (List t1) = extractPair t1
extractPair t@(Pair _ _) = t
extractPair _ = error "Type doesn't contain a pair, cannot extract pair"

pairComponents :: Type -> (Type, Type)
pairComponents (Pair t1 t2) = (t1, t2)
pairComponents t = error $ "Type is not a pair: " ++ show t

{-
tupleComponents :: Type -> [Type]
tupleComponents (Tuple ts) = ts
tupleComponents t          = error $ "Type is not a tuple type: " ++ show t
-}

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
extractShape (List t1) = \x -> listT $ extractShape t1 x
extractShape _         = \x -> x

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
unliftType (List t1) = t1
unliftType (Fn t1 t2) = Fn (unliftType t1) (unliftType t2)
unliftType t         = error $ "Type: " ++ show t ++ " cannot be unlifted."

isFuns :: Type -> Bool
isFuns (List t1) = isFuns t1
isFuns (Fn _ _) = True
-- isFuns (Tuple _) = False
isFuns (Pair _ _) = False
isFuns _         = False 

transType :: Type -> Type
transType ot@(List t) | containsTuple t = case transType t of
                                                (Pair t1 t2) -> Pair (transType $ List t1) (transType $ List t2)
                                                t' -> List t'
                        | otherwise       = ot
transType (Pair t1 t2) = Pair (transType t1) (transType t2)
transType (Fn t1 t2)   = Fn (transType t1) (transType t2)
transType t            = t

class Typed a t where
  typeOf :: a t -> t
