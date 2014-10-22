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

--------------------------------------------------------------------------------
-- Typed frontend ASTs

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

data TupleConst a where
    Tuple2E :: (Reify a, Reify b) => Exp a -> Exp b -> TupleConst (a, b)
    Tuple3E :: (Reify a, Reify b, Reify c) => Exp a -> Exp b -> Exp c -> TupleConst (a, b, c)
    Tuple4E :: (Reify a, Reify b, Reify c, Reify d) => Exp a -> Exp b -> Exp c -> Exp d -> TupleConst (a, b, c, d)
    Tuple5E :: (Reify a, Reify b, Reify c, Reify d, Reify e) => Exp a -> Exp b -> Exp c -> Exp d -> Exp e -> TupleConst (a, b, c, d, e)
    Tuple6E :: (Reify a, Reify b, Reify c, Reify d, Reify e, Reify f) => Exp a -> Exp b -> Exp c -> Exp d -> Exp e -> Exp f -> TupleConst (a, b, c, d, e, f)
    Tuple7E :: (Reify a, Reify b, Reify c, Reify d, Reify e, Reify f, Reify g) => Exp a -> Exp b -> Exp c -> Exp d -> Exp e -> Exp f -> Exp g -> TupleConst (a, b, c, d, e, f, g)
    Tuple8E :: (Reify a, Reify b, Reify c, Reify d, Reify e, Reify f, Reify g, Reify h) => Exp a -> Exp b -> Exp c -> Exp d -> Exp e -> Exp f -> Exp g -> Exp h -> TupleConst (a, b, c, d, e, f, g, h)
    Tuple9E :: (Reify a, Reify b, Reify c, Reify d, Reify e, Reify f, Reify g, Reify h, Reify i) => Exp a -> Exp b -> Exp c -> Exp d -> Exp e -> Exp f -> Exp g -> Exp h -> Exp i -> TupleConst (a, b, c, d, e, f, g, h, i)
    Tuple10E :: (Reify a, Reify b, Reify c, Reify d, Reify e, Reify f, Reify g, Reify h, Reify i, Reify j) => Exp a -> Exp b -> Exp c -> Exp d -> Exp e -> Exp f -> Exp g -> Exp h -> Exp i -> Exp j -> TupleConst (a, b, c, d, e, f, g, h, i, j)
    Tuple11E :: (Reify a, Reify b, Reify c, Reify d, Reify e, Reify f, Reify g, Reify h, Reify i, Reify j, Reify k) => Exp a -> Exp b -> Exp c -> Exp d -> Exp e -> Exp f -> Exp g -> Exp h -> Exp i -> Exp j -> Exp k -> TupleConst (a, b, c, d, e, f, g, h, i, j, k)
    Tuple12E :: (Reify a, Reify b, Reify c, Reify d, Reify e, Reify f, Reify g, Reify h, Reify i, Reify j, Reify k, Reify l) => Exp a -> Exp b -> Exp c -> Exp d -> Exp e -> Exp f -> Exp g -> Exp h -> Exp i -> Exp j -> Exp k -> Exp l -> TupleConst (a, b, c, d, e, f, g, h, i, j, k, l)
    Tuple13E :: (Reify a, Reify b, Reify c, Reify d, Reify e, Reify f, Reify g, Reify h, Reify i, Reify j, Reify k, Reify l, Reify m) => Exp a -> Exp b -> Exp c -> Exp d -> Exp e -> Exp f -> Exp g -> Exp h -> Exp i -> Exp j -> Exp k -> Exp l -> Exp m -> TupleConst (a, b, c, d, e, f, g, h, i, j, k, l, m)
    Tuple14E :: (Reify a, Reify b, Reify c, Reify d, Reify e, Reify f, Reify g, Reify h, Reify i, Reify j, Reify k, Reify l, Reify m, Reify n) => Exp a -> Exp b -> Exp c -> Exp d -> Exp e -> Exp f -> Exp g -> Exp h -> Exp i -> Exp j -> Exp k -> Exp l -> Exp m -> Exp n -> TupleConst (a, b, c, d, e, f, g, h, i, j, k, l, m, n)
    Tuple15E :: (Reify a, Reify b, Reify c, Reify d, Reify e, Reify f, Reify g, Reify h, Reify i, Reify j, Reify k, Reify l, Reify m, Reify n, Reify o) => Exp a -> Exp b -> Exp c -> Exp d -> Exp e -> Exp f -> Exp g -> Exp h -> Exp i -> Exp j -> Exp k -> Exp l -> Exp m -> Exp n -> Exp o -> TupleConst (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o)
    Tuple16E :: (Reify a, Reify b, Reify c, Reify d, Reify e, Reify f, Reify g, Reify h, Reify i, Reify j, Reify k, Reify l, Reify m, Reify n, Reify o, Reify  p) => Exp a -> Exp b -> Exp c -> Exp d -> Exp e -> Exp f -> Exp g -> Exp h -> Exp i -> Exp j -> Exp k -> Exp l -> Exp m -> Exp n -> Exp o -> Exp p -> TupleConst (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p)

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

data TupleType a where
    Tuple2T :: (Reify a, Reify b) => Type a -> Type b -> TupleType (a, b)
    Tuple3T :: (Reify a, Reify b, Reify c) => Type a -> Type b -> Type c -> TupleType (a, b, c)
    Tuple4T :: (Reify a, Reify b, Reify c, Reify d) => Type a -> Type b -> Type c -> Type d -> TupleType (a, b, c, d)
    Tuple5T :: (Reify a, Reify b, Reify c, Reify d, Reify e) => Type a -> Type b -> Type c -> Type d -> Type e -> TupleType (a, b, c, d, e)
    Tuple6T :: (Reify a, Reify b, Reify c, Reify d, Reify e, Reify f) => Type a -> Type b -> Type c -> Type d -> Type e -> Type f -> TupleType (a, b, c, d, e, f)
    Tuple7T :: (Reify a, Reify b, Reify c, Reify d, Reify e, Reify f, Reify g) => Type a -> Type b -> Type c -> Type d -> Type e -> Type f -> Type g -> TupleType (a, b, c, d, e, f, g)
    Tuple8T :: (Reify a, Reify b, Reify c, Reify d, Reify e, Reify f, Reify g, Reify h) => Type a -> Type b -> Type c -> Type d -> Type e -> Type f -> Type g -> Type h -> TupleType (a, b, c, d, e, f, g, h)
    Tuple9T :: (Reify a, Reify b, Reify c, Reify d, Reify e, Reify f, Reify g, Reify h, Reify i) => Type a -> Type b -> Type c -> Type d -> Type e -> Type f -> Type g -> Type h -> Type i -> TupleType (a, b, c, d, e, f, g, h, i)
    Tuple10T :: (Reify a, Reify b, Reify c, Reify d, Reify e, Reify f, Reify g, Reify h, Reify i, Reify j) => Type a -> Type b -> Type c -> Type d -> Type e -> Type f -> Type g -> Type h -> Type i -> Type j -> TupleType (a, b, c, d, e, f, g, h, i, j)
    Tuple11T :: (Reify a, Reify b, Reify c, Reify d, Reify e, Reify f, Reify g, Reify h, Reify i, Reify j, Reify k) => Type a -> Type b -> Type c -> Type d -> Type e -> Type f -> Type g -> Type h -> Type i -> Type j -> Type k -> TupleType (a, b, c, d, e, f, g, h, i, j, k)
    Tuple12T :: (Reify a, Reify b, Reify c, Reify d, Reify e, Reify f, Reify g, Reify h, Reify i, Reify j, Reify k, Reify l) => Type a -> Type b -> Type c -> Type d -> Type e -> Type f -> Type g -> Type h -> Type i -> Type j -> Type k -> Type l -> TupleType (a, b, c, d, e, f, g, h, i, j, k, l)
    Tuple13T :: (Reify a, Reify b, Reify c, Reify d, Reify e, Reify f, Reify g, Reify h, Reify i, Reify j, Reify k, Reify l, Reify m) => Type a -> Type b -> Type c -> Type d -> Type e -> Type f -> Type g -> Type h -> Type i -> Type j -> Type k -> Type l -> Type m -> TupleType (a, b, c, d, e, f, g, h, i, j, k, l, m)
    Tuple14T :: (Reify a, Reify b, Reify c, Reify d, Reify e, Reify f, Reify g, Reify h, Reify i, Reify j, Reify k, Reify l, Reify m, Reify n) => Type a -> Type b -> Type c -> Type d -> Type e -> Type f -> Type g -> Type h -> Type i -> Type j -> Type k -> Type l -> Type m -> Type n -> TupleType (a, b, c, d, e, f, g, h, i, j, k, l, m, n)
    Tuple15T :: (Reify a, Reify b, Reify c, Reify d, Reify e, Reify f, Reify g, Reify h, Reify i, Reify j, Reify k, Reify l, Reify m, Reify n, Reify o) => Type a -> Type b -> Type c -> Type d -> Type e -> Type f -> Type g -> Type h -> Type i -> Type j -> Type k -> Type l -> Type m -> Type n -> Type o -> TupleType (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o)
    Tuple16T :: (Reify a, Reify b, Reify c, Reify d, Reify e, Reify f, Reify g, Reify h, Reify i, Reify j, Reify k, Reify l, Reify m, Reify n, Reify o, Reify  p) => Type a -> Type b -> Type c -> Type d -> Type e -> Type f -> Type g -> Type h -> Type i -> Type j -> Type k -> Type l -> Type m -> Type n -> Type o -> Type p -> TupleType (a, b, c, d, e, f, g, h, i, j, k, l, m, n, o, p)

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
