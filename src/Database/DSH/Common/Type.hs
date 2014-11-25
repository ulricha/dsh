{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TemplateHaskell        #-}

module Database.DSH.Common.Type 
    ( isNum
    , isList
    , elemT
    , tupleElemT
    , tupleElemTypes
    , fstT
    , sndT
    , listDepth
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
    , pairT
    , Typed (..)
    ) where

import Text.PrettyPrint.ANSI.Leijen

import Database.DSH.Impossible
import Database.DSH.Common.Pretty
import Database.DSH.Common.Nat
  
instance Pretty Type where 
    pretty IntT          = text "Int"
    pretty BoolT         = text "Bool"
    pretty DoubleT       = text "Double"
    pretty StringT       = text "String"
    pretty UnitT         = text "()"
    pretty (ListT t)     = brackets $ pretty t
    pretty (TupleT ts)   = tupled $ map pretty ts

-- | We use the following type language to type the various
-- intermediate languages.
data Type  = IntT 
           | BoolT 
           | DoubleT
           | StringT 
           | UnitT 
           | ListT Type
           | TupleT [Type]
           deriving (Show, Eq, Ord)

isNum :: Type -> Bool
isNum IntT        = True
isNum DoubleT     = True
isNum BoolT       = False
isNum StringT     = False
isNum UnitT       = False
isNum (ListT _)   = False
isNum (TupleT _)  = False
      
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

listT :: Type -> Type
listT = ListT

pairT :: Type -> Type -> Type
pairT t1 t2 = TupleT [t1, t2]

isList :: Type -> Bool
isList (ListT _) = True
isList _        = False

elemT :: Type -> Type
elemT (ListT t) = t
elemT _        = error "elemT: argument is not a list type"

tupleElemT :: Type -> TupleIndex -> Type
tupleElemT (TupleT ts) f = ts !! (tupleIndex f - 1)
tupleElemT _           _ = $impossible

tupleElemTypes :: Type -> [Type]
tupleElemTypes (TupleT ts) = ts
tupleElemTypes _           = $impossible

listDepth :: Type -> Int
listDepth (ListT t1) = 1 + listDepth t1
listDepth _          = 0

fstT :: Type -> Type
fstT (TupleT [t1, _]) = t1
fstT _                = error "Type is not a pair type"

sndT :: Type -> Type
sndT (TupleT [_, t2]) = t2
sndT _                = error "Type is not a pair type"

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

class Typed a where
  typeOf :: a -> Type
