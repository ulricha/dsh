%if False
\begin{code}

{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE DeriveGeneric          #-}
{-# LANGUAGE DeriveDataTypeable     #-}

module Database.DSH.Common.Data.Type 
 ( isNum
 , extractPairT
 , isList
 , elemT
 , fstT
 , sndT
 , domainT
 , splitType
 , varsInType
 , listDepth
 , pairT
 , containsTuple
 , pairComponents
 , splitTypeArgsRes
 , extractFunTRes
 , extractFunTArgs
 , extractShape
 , unliftTypeN
 , unliftType
 , liftType
 , liftTypeN
 , Type(..)
 , intT
 , boolT
 , unitT
 , stringT
 , doubleT
 , listT
 , (.->)
 , Typed (..)
 , isFuns)
where

import Data.Data
import Data.Typeable
import GHC.Generics (Generic)
  
instance Show Type where 
    show (VarT v) = v
    show (FunT t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"
    show IntT = "IntT"
    show NatT = "NatT"
    show BoolT = "BoolT"
    show DoubleT = "DoubleT"
    show StringT = "StringT"
    show UnitT = "()"
    show (ListT t) = "[" ++ (show t) ++ "]"
    show (PairT t1 t2) = "(" ++ show t1 ++ ", " ++ show t2 ++ ")"
\end{code}
%endif
%{
We use the following type language to type our input language with (the Nested Kernel Language). We also use this type scheme for several intermediate languages.

%include syntaxdef.fmt
%include types.fmt
%format (VarT (x)) = " x "
%format NatT = " \const{NatT}"
  
\newcommand{\typeLang}{
\begin{code}
data Type  = FunT Type Type
           | NatT | IntT | BoolT | DoubleT
           | StringT | UnitT | VarT String
           | PairT Type Type |  ListT Type
\end{code}
}
\typeLang
%}
%if False
\begin{code}
    deriving (Eq, Ord, Generic, Data, Typeable)

infixr 6 .->

isNum :: Type -> Bool
isNum IntT = True
isNum NatT = True
isNum DoubleT = True
isNum (VarT _) = False
isNum (FunT _ _) = False
isNum BoolT = False
isNum StringT = False
isNum UnitT = False
isNum (ListT _) = False
isNum (PairT _ _) = False
      
domainT :: Type -> Type
domainT (FunT t _) = t
domainT _          = error "domainT: argument is not a function type"

varsInType :: Type -> [String]
varsInType (FunT t1 t2) = varsInType t1 ++ varsInType t2
varsInType (PairT t1 t2) = varsInType t1 ++ varsInType t2
varsInType (ListT t) = varsInType t
varsInType (VarT v) = [v]
varsInType _ = []

(.->) :: Type -> Type -> Type
t1 .-> t2 = FunT t1 t2

intT :: Type
intT = IntT

stringT :: Type
stringT = StringT

doubleT :: Type
doubleT = DoubleT

boolT :: Type
boolT = BoolT

unitT :: Type
unitT = UnitT

pairT :: Type -> Type -> Type
pairT t1 t2 = PairT t1 t2

listT :: Type -> Type
listT = ListT

isList :: Type -> Bool
isList (ListT _) = True
isList _        = False

elemT :: Type -> Type
elemT (ListT t) = t
elemT _        = error "elemT: argument is not a list type"

listDepth :: Type -> Int
listDepth (ListT t1) = 1 + listDepth t1
listDepth _          = 0

containsTuple :: Type -> Bool
containsTuple (FunT t1 t2) = containsTuple t1 || containsTuple t2
containsTuple (PairT _ _)  = True
containsTuple (ListT t)    = containsTuple t
containsTuple _            = False

extractPairT :: Type -> Type
extractPairT (ListT t1) = extractPairT t1
extractPairT t@(PairT _ _) = t
extractPairT _ = error "Type doesn't contain a pair, cannot extract pair"

fstT :: Type -> Type
fstT (PairT t1 _) = t1
fstT _            = error "Type is not a pair type"

sndT :: Type -> Type
sndT (PairT _ t2) = t2
sndT _            = error "Type is not a pair type"

pairComponents :: Type -> (Type, Type)
pairComponents (PairT t1 t2) = (t1, t2)
pairComponents t = error $ "Type is not a pair: " ++ show t

extractFunTRes :: Type -> Type
extractFunTRes = snd . splitTypeArgsRes

extractFunTArgs :: Type -> [Type]
extractFunTArgs = fst . splitTypeArgsRes

splitTypeArgsRes :: Type -> ([Type], Type)
splitTypeArgsRes (FunT t1 t2) = let (args, r) = splitTypeArgsRes t2 in (t1:args, r)
splitTypeArgsRes t          = ([], t)

splitType :: Type -> (Type, Type)
splitType (FunT t1 t2) = (t1, t2)
splitType _          = error "Can only split function types"

extractShape :: Type -> Type -> Type
extractShape (ListT t1) = \x -> listT $ extractShape t1 x
extractShape _         = \x -> x

liftTypeN :: Int -> Type -> Type
liftTypeN 0 t = t
liftTypeN i t = liftTypeN (i - 1) $ liftType t

liftType :: Type -> Type
-- liftType (FunT t1 t2) = FunT (liftType t1) (liftType t2)
liftType t = listT t 

unliftTypeN :: Int -> Type -> Type
unliftTypeN 0 t = t
unliftTypeN i t = unliftTypeN (i - 1) $ unliftType t

unliftType :: Type -> Type
unliftType (ListT t1) = t1
-- unliftType (FunT t1 t2) = FunT (unliftType t1) (unliftType t2)
unliftType t         = error $ "Type: " ++ show t ++ " cannot be unlifted."

isFuns :: Type -> Bool
isFuns (ListT t1) = isFuns t1
isFuns (FunT _ _) = True
isFuns (PairT _ _) = False
isFuns _         = False 


class Typed a where
  typeOf :: a -> Type
\end{code}
%endif
