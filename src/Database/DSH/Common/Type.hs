{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TemplateHaskell        #-}

module Database.DSH.Common.Type 
    ( isNum
    , extractPairT
    , isList
    , elemT
    , tupleElemT
    , fstT
    , sndT
    , domainT
    , splitType
    , listDepth
    , pairT
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
    , isFuns
    ) where

import Text.PrettyPrint.ANSI.Leijen

import Database.DSH.Impossible
import Database.DSH.Common.Pretty
import Database.DSH.Common.Nat
  
instance Pretty Type where 
    pretty (FunT t1 t2)  = parens $ pretty t1 <+> text "->" <+> pretty t2
    pretty IntT          = text "Int"
    pretty BoolT         = text "Bool"
    pretty DoubleT       = text "Double"
    pretty StringT       = text "String"
    pretty UnitT         = text "()"
    pretty (ListT t)     = brackets $ pretty t
    pretty (PairT t1 t2) = parens $ pretty t1 <> comma <+> pretty t2
    pretty (TupleT ts)   = tupled $ map pretty ts

-- | We use the following type language to type the various
-- intermediate languages.
data Type  = FunT Type Type
           | IntT 
           | BoolT 
           | DoubleT
           | StringT 
           | UnitT 
           | PairT Type Type 
           | ListT Type
           | TupleT [Type]
           deriving (Show, Eq, Ord)

infixr 6 .->

isNum :: Type -> Bool
isNum IntT        = True
isNum DoubleT     = True
isNum (FunT _ _)  = False
isNum BoolT       = False
isNum StringT     = False
isNum UnitT       = False
isNum (ListT _)   = False
isNum (PairT _ _) = False
isNum (TupleT _)  = False
      
domainT :: Type -> Type
domainT (FunT t _) = t
domainT _          = error "domainT: argument is not a function type"

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

tupleElemT :: Type -> TupleIndex -> Type
tupleElemT (TupleT ts) f = ts !! (tupleIndex f - 1)
tupleElemT _           _ = $impossible

listDepth :: Type -> Int
listDepth (ListT t1) = 1 + listDepth t1
listDepth _          = 0

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
pairComponents t = error $ "Type is not a pair: " ++ pp t

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
extractShape _          = \x -> x

liftTypeN :: Nat -> Type -> Type
liftTypeN Zero t     = t
liftTypeN (Succ n) t = liftTypeN n $ liftType t

liftType :: Type -> Type
liftType t = listT t 

unliftTypeN :: Nat -> Type -> Type
unliftTypeN Zero t     = t
unliftTypeN (Succ n) t = unliftTypeN n $ unliftType t

unliftType :: Type -> Type
unliftType (ListT t1) = t1
unliftType t          = error $ "Type: " ++ pp t ++ " cannot be unlifted."

isFuns :: Type -> Bool
isFuns (ListT t1) = isFuns t1
isFuns (FunT _ _) = True
isFuns (PairT _ _) = False
isFuns _         = False 

class Typed a where
  typeOf :: a -> Type