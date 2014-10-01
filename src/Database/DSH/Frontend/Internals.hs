{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE TypeFamilies              #-}
{-# LANGUAGE TemplateHaskell           #-}

module Database.DSH.Frontend.Internals where

import Data.Text (Text)
import Text.Printf

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
  PairE       :: (Reify a, Reify b)  => Exp a -> Exp b -> Exp (a,b)
  ListE       :: (Reify a)           => [Exp a] -> Exp [a]
  AppE        :: (Reify a, Reify b)  => Fun a b -> Exp a -> Exp b
  LamE        :: (Reify a, Reify b)  => (Exp a -> Exp b) -> Exp (a -> b)
  VarE        :: (Reify a)           => Integer -> Exp a
  TableE      :: (Reify a)           => Table -> Exp [a]
  TupleConstE :: TupleConst a -> Exp a

data TupleConst a where
    Tuple2E :: (Reify a, Reify b) => Exp a -> Exp b -> TupleConst (a, b)
    Tuple3E :: (Reify a, Reify b, Reify c) => Exp a -> Exp b -> Exp c -> TupleConst (a, b, c)

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
  PairT     :: (Reify a,Reify b)  => Type a -> Type b -> Type (a,b)
  ListT     :: (Reify a)          => Type a -> Type [a]
  ArrowT    :: (Reify a,Reify b)  => Type a -> Type b -> Type (a -> b)
  TupleT    :: TupleType a -> Type a

data TupleType a where
    Tuple2T :: (Reify a, Reify b) => Type a -> Type b -> TupleType (a, b)
    Tuple3T :: (Reify a, Reify b, Reify c) => Type a -> Type b -> Type c -> TupleType (a, b, c)
    Tuple4T :: (Reify a, Reify b, Reify c, Reify d) => Type a -> Type b -> Type c -> Type d -> TupleType (a, b, c, d)

-- Show instances

instance Show (Type a) where
  show UnitT = "()"
  show BoolT = "Bool"
  show CharT = "Char"
  show IntegerT = "Integer"
  show DoubleT = "Double"
  show TextT = "Text"
  show (PairT l r) = "(" ++ show l ++ ", " ++ show r ++ ")"
  show (ListT t) = "[" ++ show t ++ "]"
  show (ArrowT t1 t2) = "(" ++ show t1 ++ " -> " ++ show t2 ++ ")"

instance Show (Fun a b) where
    show Fst = "fst"
    show Snd = "snd"
    show Not = "not"
    show Concat = "concat"
    show Head = "head"
    show Tail = "tail"
    show Init = "init"
    show Last = "last"
    show Null = "null"
    show Length = "length"
    show Reverse = "reverse"
    show And = "and"
    show Or = "or"
    show Sum = "sum"
    show Avg = "avg"
    show Maximum = "maximum"
    show Minimum = "minimum"
    show Nub = "nub"
    show IntegerToDouble = "integerToDouble"
    show Add = "+"
    show Mul = "*"
    show Sub = "-"
    show Div = "/"
    show Lt  = "<"
    show Lte = "<="
    show Equ = "=="
    show NEq = "/="
    show Gte = ">="
    show Gt  = ">"
    show Conj = "&&"
    show Disj = "||"
    show Cons = "cons"
    show Index = "index"
    show Zip = "zip"
    show Map = "map"
    show ConcatMap = "concatMap"
    show Filter = "filter"
    show GroupWithKey = "groupWithKey"
    show SortWith = "sortWith"
    show Cond = "cond"
    show Append = "append"
    show Like = "like"
    show Mod = "%"
    show Number = "number"
    show Guard = "guard"
    show (Reshape n) = printf "reshape(%d)" n
    show Transpose = "transpose"
    show Sin = "sin"
    show Cos = "cos"
    show Tan = "tan"
    show Sqrt = "sqrt"
    show Exp = "exp"
    show Log = "log"
    show ASin = "asin"
    show ACos = "acos"
    show ATan = "atan"

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

instance (Reify a, Reify b) => Reify (a,b) where
  reify _ = PairT (reify (undefined :: a)) (reify (undefined :: b))

instance (Reify a, Reify b, Reify c) => Reify (a, b, c) where
    reify _ = TupleT $ Tuple3T (reify (undefined :: a)) (reify (undefined :: b)) (reify (undefined :: c))

instance (Reify a) => Reify [a] where
  reify _ = ListT (reify (undefined :: a))

instance (Reify a, Reify b) => Reify (a -> b) where
  reify _ = ArrowT (reify (undefined :: a)) (reify (undefined :: b))

-- Utility functions

unQ :: Q a -> Exp (Rep a)
unQ (Q e) = e

toLam :: (QA a,QA b) => (Q a -> Q b) -> Exp (Rep a) -> Exp (Rep b)
toLam f = unQ . f . Q

$(mkReifyInstances 4)
