{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TemplateHaskell           #-}
{-# LANGUAGE ScopedTypeVariables       #-}

module Database.DSH.Frontend.Internals where

import Data.Text (Text)

import Database.DSH.Frontend.Funs
import Database.DSH.Frontend.TupleTypes


--------------------------------------------------------------------------------
-- Typed frontend ASTs

-- Generate the data types 'TupleConst' and 'TupleType' for tuple term
-- and type construction.
$(mkTupleAstComponents 16)

data Exp a where
  UnitE       :: Exp ()
  BoolE       :: Bool    -> Exp Bool
  CharE       :: Char    -> Exp Char
  IntegerE    :: Integer -> Exp Integer
  DoubleE     :: Double  -> Exp Double
  TextE       :: Text    -> Exp Text
  ListE       :: (Reify a)           => [Exp a] -> Exp [a]
  AppE        :: (Reify a, Reify b)  => Fun a b -> Exp a -> Exp b
  LamE        :: (Reify a, Reify b)  => (Exp a -> Exp b) -> Exp (a -> b)
  VarE        :: (Reify a)           => Integer -> Exp a
  TableE      :: (Reify a)           => Table -> Exp [a]
  TupleConstE :: TupleConst a -> Exp a

data Type a where
  UnitT     :: Type ()
  BoolT     :: Type Bool
  CharT     :: Type Char
  IntegerT  :: Type Integer
  DoubleT   :: Type Double
  TextT     :: Type Text
  ListT     :: (Reify a)          => Type a -> Type [a]
  ArrowT    :: (Reify a,Reify b)  => Type a -> Type b -> Type (a -> b)
  TupleT    :: TupleType a -> Type a

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

-- | A combination of column names that form a candidate key
newtype Key = Key [String] deriving (Eq, Ord, Show)

-- | Is the table guaranteed to be not empty?
data Emptiness = NonEmpty
               | PossiblyEmpty
               deriving (Eq, Ord, Show)

-- | Catalog information hints that users may give to DSH
data TableHints = TableHints 
    { keysHint     :: [Key]
    , nonEmptyHint :: Emptiness
    } deriving (Eq, Ord, Show)

data Table = TableDB String TableHints

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

instance Reify Text where
  reify _ = TextT

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
