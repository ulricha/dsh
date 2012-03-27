%if False
\begin{code}
{-# LANGUAGE GADTs, TypeSynonymInstances, MultiParamTypeClasses #-}
module Language.ParallelLang.Common.Data.Type 
 (isNum, transType, extractPair, isListT, splitType, varsInType, listDepth, pairT, containsTuple, pairComponents, splitTypeArgsRes, extractFnRes, extractFnArgs, extractShape, unliftTypeN, unliftType, liftType, liftTypeN, Type(..), intT, boolT, unitT, stringT, doubleT, listT, (.->), Typed (..), isFuns)
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
    show (Pair t1 t2) = "(" ++ show t1 ++ ", " ++ show t2 ++ ")"
\end{code}
%endif
%{
We use the following type language to type our input language with (the Nested Kernel Language). We also use this type scheme for several intermediate languages.

%include syntaxdef.fmt
%include types.fmt
%format (Var (x)) = " x "
%format Nat = " \const{Nat}"
  
\newcommand{\typeLang}{
\begin{code}
data Type  =  Fn Type Type
           |  Nat | Int | Bool |  Double
           |  String | Unit | Var String
           |  Pair Type Type |  List Type
\end{code}
}
\typeLang
%}
%if False
\begin{code}
    deriving (Eq, Ord)

infixr 6 .->

isNum :: Type -> Bool
isNum Int = True
isNum Nat = True
isNum Double = True
isNum (Var _) = False
isNum (Fn _ _) = False
isNum Bool = False
isNum String = False
isNum Unit = False
isNum (List _) = False
isNum (Pair _ _) = False

varsInType :: Type -> [String]
varsInType (Fn t1 t2) = varsInType t1 ++ varsInType t2
varsInType (Pair t1 t2) = varsInType t1 ++ varsInType t2
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

listT :: Type -> Type
listT = List

isListT :: Type -> Bool
isListT (List _) = True
isListT _        = False

listDepth :: Type -> Int
listDepth (List t1) = 1 + listDepth t1
listDepth _                 = 0

containsTuple :: Type -> Bool
containsTuple (Fn t1 t2) = containsTuple t1 || containsTuple t2
containsTuple (Pair _ _)  = True
containsTuple (List t)   = containsTuple t
containsTuple _          = False

extractPair :: Type -> Type
extractPair (List t1) = extractPair t1
extractPair t@(Pair _ _) = t
extractPair _ = error "Type doesn't contain a pair, cannot extract pair"

pairComponents :: Type -> (Type, Type)
pairComponents (Pair t1 t2) = (t1, t2)
pairComponents t = error $ "Type is not a pair: " ++ show t

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
-- liftType (Fn t1 t2) = Fn (liftType t1) (liftType t2)
liftType t = listT t 

unliftTypeN :: Int -> Type -> Type
unliftTypeN 0 t = t
unliftTypeN i t = unliftTypeN (i - 1) $ unliftType t

unliftType :: Type -> Type
unliftType (List t1) = t1
-- unliftType (Fn t1 t2) = Fn (unliftType t1) (unliftType t2)
unliftType t         = error $ "Type: " ++ show t ++ " cannot be unlifted."

isFuns :: Type -> Bool
isFuns (List t1) = isFuns t1
isFuns (Fn _ _) = True
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

class Typed a where
  typeOf :: a -> Type
\end{code}
%endif