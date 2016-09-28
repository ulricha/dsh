{-# LANGUAGE AllowAmbiguousTypes   #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeSynonymInstances  #-}

{-# OPTIONS_GHC -Wno-redundant-constraints #-}

module Database.DSH.Frontend.Internals where

import qualified Data.Sequence as S
import           Data.Decimal
import           Data.Scientific
import           Data.List.NonEmpty               (NonEmpty)
import           Data.Text                        (Text)
import           Data.Time.Calendar               (Day)
import           Text.PrettyPrint.ANSI.Leijen

import           Database.DSH.Common.Impossible
import           Database.DSH.Frontend.Builtins
import           Database.DSH.Frontend.TupleTypes

--------------------------------------------------------------------------------
-- Typed frontend ASTs

-- Generate the data types 'TupleConst' and 'TupleType' for tuple term
-- and type construction.
$(mkTupleAstComponents 16)

data Exp a where
    UnitE       :: Exp ()
    BoolE       :: !Bool    -> Exp Bool
    CharE       :: !Char    -> Exp Char
    IntegerE    :: !Integer -> Exp Integer
    DoubleE     :: !Double  -> Exp Double
    TextE       :: !Text    -> Exp Text
    DecimalE    :: !Decimal -> Exp Decimal
    ScientificE :: !Scientific -> Exp Scientific
    DayE        :: !Day     -> Exp Day
    ListE       :: (Reify a)           => !(S.Seq (Exp a)) -> Exp [a]
    AppE        :: (Reify a, Reify b)  => Fun a b -> Exp a -> Exp b
    LamE        :: (Reify a, Reify b)  => (Exp a -> Exp b) -> Exp (a -> b)
    VarE        :: (Reify a)           => Integer -> Exp a
    TableE      :: (Reify a)           => Table -> Exp [a]
    TupleConstE :: !(TupleConst a) -> Exp a

data Type a where
    UnitT       :: Type ()
    BoolT       :: Type Bool
    CharT       :: Type Char
    IntegerT    :: Type Integer
    DoubleT     :: Type Double
    TextT       :: Type Text
    DecimalT    :: Type Decimal
    ScientificT :: Type Scientific
    DayT        :: Type Day
    ListT       :: (Reify a)          => Type a -> Type [a]
    ArrowT      :: (Reify a,Reify b)  => Type a -> Type b -> Type (a -> b)
    TupleT      :: TupleType a -> Type a

instance Pretty (Type a) where
    pretty UnitT          = text "()"
    pretty BoolT          = text "Bool"
    pretty CharT          = text "Char"
    pretty IntegerT       = text "Integer"
    pretty DoubleT        = text "Double"
    pretty TextT          = text "Text"
    pretty DecimalT       = text "Decimal"
    pretty ScientificT    = text "Scientific"
    pretty DayT           = text "Day"
    pretty (ListT t)      = brackets $ pretty t
    pretty (ArrowT t1 t2) = parens $ pretty t1 <+> text "->" <+> pretty t2
    pretty (TupleT t)     = pretty t

-- FIXME generate with TH
instance Pretty (TupleType a) where
    pretty (Tuple2T t1 t2) = tupled [pretty t1, pretty t2]
    pretty _               = $unimplemented

--------------------------------------------------------------------------------
-- Classes

class Reify a where
    reify :: a -> Type a

class (Reify (Rep a)) => QA a where
    type Rep a
    toExp :: a -> Exp (Rep a)
    frExp :: Exp (Rep a) -> a

class (QA a,QA r) => Elim a r where
    type Eliminator a r
    elim :: Q a -> Eliminator a r

class BasicType a where

class TA a where

class View a where
    type ToView a
    view :: a -> ToView a

newtype Q a = Q (Exp (Rep a))

pairE :: (Reify a, Reify b) => Exp a -> Exp b -> Exp (a, b)
pairE a b = TupleConstE (Tuple2E a b)

tripleE :: (Reify a, Reify b, Reify c) => Exp a -> Exp b -> Exp c -> Exp (a, b, c)
tripleE a b c = TupleConstE (Tuple3E a b c)

--------------------------------------------------------------------------------
-- Definition of database-resident tables

-- | A combination of column names that form a candidate key
newtype Key = Key (NonEmpty String) deriving (Eq, Ord, Show)

-- | Is the table guaranteed to be not empty?
data Emptiness = NonEmpty
               | PossiblyEmpty
               deriving (Eq, Ord, Show)

type ColName = String

-- | Catalog information hints that users may give to DSH
data TableHints = TableHints
    { keysHint     :: NonEmpty Key
    , nonEmptyHint :: Emptiness
    } deriving (Eq, Ord, Show)

data Table = TableDB String (NonEmpty ColName) TableHints

-- Reify instances

instance Reify () where
    reify _ = UnitT

instance Reify Bool where
    reify _ = BoolT

instance Reify Char where
    reify _ = CharT

instance Reify Integer where
    reify _ = IntegerT

instance Reify Double where
    reify _ = DoubleT

instance Reify Decimal where
    reify _ = DecimalT

instance Reify Scientific where
    reify _ = ScientificT

instance Reify Text where
    reify _ = TextT

instance Reify Day where
  reify _ = DayT

instance (Reify a) => Reify [a] where
    reify _ = ListT (reify (undefined :: a))

instance (Reify a, Reify b) => Reify (a -> b) where
    reify _ = ArrowT (reify (undefined :: a)) (reify (undefined :: b))

-- Utility functions

unQ :: Q a -> Exp (Rep a)
unQ (Q e) = e

toLam :: (QA a,QA b) => (Q a -> Q b) -> Exp (Rep a) -> Exp (Rep b)
toLam f = unQ . f . Q

-- * Generate Reify instances for tuple types
mkReifyInstances 16
