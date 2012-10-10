module Database.DSH.Internals where

import Database.DSH.Impossible

import Data.Text (Text)

data Exp a where
  UnitE     :: Exp ()
  BoolE     :: Bool    -> Exp Bool
  CharE     :: Char    -> Exp Char
  IntegerE  :: Integer -> Exp Integer
  DoubleE   :: Double  -> Exp Double
  TextE     :: Text    -> Exp Text
  PairE     :: (Reify a, Reify b)  => Exp a -> Exp b -> Exp (a,b)
  ListE     :: (Reify a)           => [Exp a] -> Exp [a]
  AppE      :: (Reify a, Reify b)  => Fun a b -> Exp a -> Exp b
  LamE      :: (Reify a, Reify b)  => (Exp a -> Exp b) -> Exp (a -> b)
  VarE      :: (Reify a)           => Integer -> Exp a
  TableE    :: (Reify a)           => Table -> Exp [a]

data Table = TableDB String [[String]] | TableCSV  String deriving (Eq, Ord, Show)

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

data Fun a b where
    Not             :: Fun Bool Bool
    IntegerToDouble :: Fun Integer Double
    And             :: Fun [Bool] Bool
    Or              :: Fun [Bool] Bool
    Concat          :: (Reify a) => Fun [[a]] [a]
    Head            :: Fun [a] a
    Tail            :: Fun [a] [a]
    The             :: Fun [a] a
    Init            :: Fun [a] [a]
    Last            :: Fun [a] a
    Null            :: Fun [a] Bool
    Length          :: Fun [a] Integer
    Reverse         :: Fun [a] [a]
    Fst             :: Fun (a,b) a
    Snd             :: Fun (a,b) b
    Sum             :: Fun [a] a
    Maximum         :: Fun [a] a
    Minimum         :: Fun [a] a
    Unzip           :: (Reify a,Reify b) => Fun [(a,b)] ([a],[b])
    Nub             :: Fun [a] [a]
    Add             :: Fun (a,a) a
    Mul             :: Fun (a,a) a
    Sub             :: Fun (a,a) a
    Div             :: Fun (a,a) a
    Lt              :: Fun (a,a) Bool
    Lte             :: Fun (a,a) Bool
    Equ             :: Fun (a,a) Bool
    Gte             :: Fun (a,a) Bool
    Gt              :: Fun (a,a) Bool
    Conj            :: Fun (Bool,Bool) Bool
    Disj            :: Fun (Bool,Bool) Bool
    Min             :: Fun (a,a) a
    Max             :: Fun (a,a) a
    Cons            :: Fun (a,[a]) [a]
    Take            :: Fun (Integer,[a]) [a]
    Drop            :: Fun (Integer,[a]) [a]
    Index           :: Fun ([a],Integer) a
    SplitAt         :: Fun (Integer,[a]) ([a],[a])
    Zip             :: Fun ([a],[b]) [(a,b)]
    Map             :: Fun (a -> b,[a]) [b]
    Filter          :: Fun (a -> Bool,[a]) [a]
    GroupWith       :: (Reify b) => Fun (a -> b,[a]) [[a]]
    SortWith        :: Fun (a -> b,[a]) [a]
    TakeWhile       :: Fun (a -> Bool,[a]) [a]
    DropWhile       :: Fun (a -> Bool,[a]) [a]
    Cond            :: Fun (Bool,(a,a)) a

data Q a where
  Q :: Exp (Rep a) -> Q a

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

class (ToView a ~ b, FromView b ~ a) => View a b where
  type ToView a
  type FromView b
  view :: a -> b
  fromView :: b -> a

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
    show The = "the"
    show Init = "init"
    show Last = "last"
    show Null = "null"
    show Length = "length"
    show Reverse = "reverse"
    show And = "and"
    show Or = "or"
    show Sum = "sum"
    show Maximum = "maximum"
    show Minimum = "minimum"
    show Unzip = "unzip"
    show Nub = "nub"
    show IntegerToDouble = "integerToDouble"
    show Add = "+"
    show Mul = "*"
    show Sub = "-"
    show Div = "/"
    show Lt  = "<"
    show Lte = "<="
    show Equ = "=="
    show Gte = ">="
    show Gt  = ">"
    show Conj = "&&"
    show Disj = "||"
    show Min  = "min"
    show Max  = "max"
    show Cons = "cons"
    show Take = "take"
    show Drop = "drop"
    show Index = "index"
    show SplitAt = "splitAt"
    show Zip = "zip"
    show Map = "map"
    show Filter = "filter"
    show GroupWith = "groupWith"
    show SortWith = "sortWith"
    show TakeWhile = "takeWhile"
    show DropWhile = "dropWhile"
    show Cond = "cond"

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

instance (Reify a) => Reify [a] where
  reify _ = ListT (reify (undefined :: a))

instance (Reify a, Reify b) => Reify (a -> b) where
  reify _ = ArrowT (reify (undefined :: a)) (reify (undefined :: b))


-- Utility functions

unQ :: Q a -> Exp (Rep a)
unQ (Q e) = e

toLam :: (QA a,QA b) => (Q a -> Q b) -> Exp (Rep a) -> Exp (Rep b)
toLam f = unQ . f . Q