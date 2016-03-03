{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE TypeSynonymInstances   #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TemplateHaskell        #-}
{-# LANGUAGE PatternSynonyms        #-}

-- | Types for backend languages.
module Database.DSH.Common.Type
    ( isNum
    , scalarType
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
    , ScalarType(..)
    , pattern PIntT
    , pattern PBoolT
    , pattern PUnitT
    , pattern PStringT
    , pattern PDoubleT
    , pattern PDecimalT
    , pattern PScientificT
    , pattern PDateT
    , pattern PPairT
    , Typed (..)
    ) where

import Debug.Trace

import Data.Aeson.TH

import Text.PrettyPrint.ANSI.Leijen

import Database.DSH.Common.Impossible
import Database.DSH.Common.Pretty
import Database.DSH.Common.Nat

instance Pretty Type where
    pretty (ListT t)     = brackets $ pretty t
    pretty (TupleT ts)   = tupled $ map pretty ts
    pretty (ScalarT t)   = pretty t

instance Pretty ScalarType where
    pretty IntT          = text "Int"
    pretty DecimalT      = text "Decimal"
    pretty ScientificT   = text "Scientific"
    pretty BoolT         = text "Bool"
    pretty DoubleT       = text "Double"
    pretty StringT       = text "String"
    pretty UnitT         = text "()"
    pretty DateT         = text "Date"

-- | We use the following type language to type the various
-- intermediate languages.
data Type  = ListT Type
           | TupleT [Type]
           | ScalarT ScalarType
           deriving (Show, Eq, Ord)


data ScalarType  = IntT
                 | BoolT
                 | DoubleT
                 | StringT
                 | UnitT
                 | DecimalT
                 | ScientificT
                 | DateT
                 deriving (Show, Eq, Ord)


-- | Is the (scalar) type numeric?
isNum :: Type -> Bool
isNum (ListT _)   = False
isNum (TupleT _)  = False
isNum (ScalarT IntT)        = True
isNum (ScalarT DoubleT)     = True
isNum (ScalarT DecimalT)    = True
isNum (ScalarT ScientificT) = True
isNum (ScalarT BoolT)       = False
isNum (ScalarT StringT)     = False
isNum (ScalarT UnitT)       = False
isNum (ScalarT DateT)       = False

scalarType :: Type -> Maybe ScalarType
scalarType (ScalarT t) = Just t
scalarType _           = Nothing

--------------------------------------------------------------------------------
-- Smart constructors and deconstructors.

pattern PIntT        = ScalarT IntT
pattern PStringT     = ScalarT StringT
pattern PDoubleT     = ScalarT DoubleT
pattern PDecimalT    = ScalarT DecimalT
pattern PScientificT = ScalarT ScientificT
pattern PBoolT       = ScalarT BoolT
pattern PDateT       = ScalarT DateT
pattern PUnitT       = ScalarT UnitT

pattern PPairT t1 t2 = TupleT [t1, t2]

isList :: Type -> Bool
isList (ListT _) = True
isList _         = False

elemT :: Type -> Type
elemT (ListT t) = t
elemT _        = error "elemT: argument is not a list type"

tupleElemT :: Type -> TupleIndex -> Type
tupleElemT (TupleT ts) f = ts !! (tupleIndex f - 1)
tupleElemT _           _ = $impossible

tupleElemTypes :: Type -> [Type]
tupleElemTypes (TupleT ts) = ts
tupleElemTypes t           = trace (show t) $ $impossible

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
extractShape (ListT t1) = \x -> ListT $ extractShape t1 x
extractShape _          = \x -> x

liftTypeN :: Nat -> Type -> Type
liftTypeN Zero t     = t
liftTypeN (Succ n) t = liftTypeN n $ liftType t

liftType :: Type -> Type
liftType t = ListT t

unliftTypeN :: Nat -> Type -> Type
unliftTypeN Zero t     = t
unliftTypeN (Succ n) t = unliftTypeN n $ unliftType t

unliftType :: Type -> Type
unliftType (ListT t1) = t1
unliftType t          = error $ "Type: " ++ pp t ++ " cannot be unlifted."

--------------------------------------------------------------------------------

-- | Typed terms
class Typed a where
  typeOf :: a -> Type

--------------------------------------------------------------------------------
-- Aeson instances for JSON serialization

$(deriveJSON defaultOptions ''ScalarType)
