module Database.DSH.Data where

import Data.String
import Data.Text (Text)
import qualified Data.Text as T
import Database.DSH.Impossible

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

class Reify a where
  reify :: a -> Type a

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

data Q a where
  Q :: Exp (Rep a) -> Q a

unQ :: Q a -> Exp (Rep a)
unQ (Q e) = e

toLam :: (QA a,QA b) => (Q a -> Q b) -> Exp (Rep a) -> Exp (Rep b)
toLam f = unQ . f . Q

class (Reify (Rep a)) => QA a where
  type Rep a
  toExp :: a -> Exp (Rep a)
  frExp :: Exp (Rep a) -> a

instance QA () where
  type Rep () = ()
  toExp () = UnitE
  frExp UnitE = ()
  frExp _ = $impossible

instance QA Bool where
  type Rep Bool = Bool
  toExp = BoolE
  frExp (BoolE b) = b
  frExp _ = $impossible

instance QA Char where
  type Rep Char = Char
  toExp = CharE
  frExp (CharE c) = c
  frExp _ = $impossible

instance QA Integer where
  type Rep Integer = Integer
  toExp = IntegerE
  frExp (IntegerE i) = i
  frExp _ = $impossible

instance QA Double where
  type Rep Double = Double
  toExp = DoubleE
  frExp (DoubleE d) = d
  frExp _ = $impossible

instance QA Text where
  type Rep Text = Text
  toExp = TextE
  frExp (TextE t) = t
  frExp _ = $impossible

instance (QA a, QA b) => QA (a,b) where
  type Rep (a,b) = (Rep a,Rep b)
  toExp (a,b) = PairE (toExp a) (toExp b)
  frExp (PairE a b) = (frExp a,frExp b)
  frExp _ = $impossible

instance (QA a) => QA [a] where
  type Rep [a] = [Rep a]
  toExp as = ListE (map toExp as)
  frExp (ListE as) = map frExp as
  frExp _ = $impossible

instance (QA a) => QA (Maybe a) where
  type Rep (Maybe a) = [Rep a]
  toExp Nothing = ListE []
  toExp (Just a) = ListE [toExp a]
  frExp (ListE []) = Nothing
  frExp (ListE (a : _)) = Just (frExp a)
  frExp _ = $impossible

instance (QA a,QA b) => QA (Either a b) where
  type Rep (Either a b) = ([Rep a],[Rep b])
  toExp (Left a) = PairE (ListE [toExp a]) (ListE [])
  toExp (Right b) = PairE (ListE []) (ListE [toExp b])
  frExp (PairE (ListE (a : _)) _) = Left (frExp a)
  frExp (PairE _ (ListE (a : _))) = Right (frExp a)
  frExp _ = $impossible

-- * Basic Types

class BasicType a where

instance BasicType () where
instance BasicType Bool where
instance BasicType Char where
instance BasicType Integer where
instance BasicType Double where
instance BasicType Text where

-- * Refering to database-resident tables

class TA a where

instance TA () where
instance TA Bool where
instance TA Char where
instance TA Integer where
instance TA Double where
instance TA Text where
instance (BasicType a, BasicType b) => TA (a,b) where

table :: (QA a, TA a) => String -> Q [a]
table name = Q (TableE (TableDB name []))

tableDB :: (QA a, TA a) => String -> Q [a]
tableDB name = Q (TableE (TableDB name []))

tableWithKeys :: (QA a, TA a) => String -> [[String]] -> Q [a]
tableWithKeys name keys = Q (TableE (TableDB name keys))

tableCSV :: (QA a, TA a) => String -> Q [a]
tableCSV filename = Q (TableE (TableCSV filename))

-- * Eq, Ord and Num Instances for Databse Queries

instance Num (Exp Integer) where
  (+) e1 e2 = AppE Add (PairE e1 e2)
  (*) e1 e2 = AppE Mul (PairE e1 e2)
  (-) e1 e2 = AppE Sub (PairE e1 e2)

  fromInteger = IntegerE

  abs e = let c = AppE Lt (PairE e 0)
          in  AppE Cond (PairE c (PairE (negate e) e))

  signum e = let c1 = AppE Lt  (PairE e 0)
                 c2 = AppE Equ (PairE e 0)
                 e' = AppE Cond (PairE c2 (PairE 0 1))
             in  AppE Cond (PairE c1 (PairE (-1) e'))

instance Num (Exp Double) where
  (+) e1 e2 = AppE Add (PairE e1 e2)
  (*) e1 e2 = AppE Mul (PairE e1 e2)
  (-) e1 e2 = AppE Sub (PairE e1 e2)

  fromInteger = DoubleE . fromInteger

  abs e = let c = AppE Lt (PairE e 0)
          in  AppE Cond (PairE c (PairE (negate e) e))

  signum e = let c1 = AppE Lt  (PairE e 0.0)
                 c2 = AppE Equ (PairE e 0.0)
                 e' = AppE Cond (PairE c2 (PairE 0 1))
             in  AppE Cond (PairE c1 (PairE (-1) e'))

instance Fractional (Exp Double) where
  (/) e1 e2    = AppE Div (PairE e1 e2)
  fromRational = DoubleE . fromRational

instance Num (Q Integer) where
  (+) (Q e1) (Q e2) = Q (e1 + e2)
  (*) (Q e1) (Q e2) = Q (e1 * e2)
  (-) (Q e1) (Q e2) = Q (e1 - e2)
  fromInteger       = Q . IntegerE
  abs (Q e)         = Q (abs e)
  signum (Q e)      = Q (signum e)

instance Num (Q Double) where
  (+) (Q e1) (Q e2) = Q (e1 + e2)
  (*) (Q e1) (Q e2) = Q (e1 * e2)
  (-) (Q e1) (Q e2) = Q (e1 - e2)
  fromInteger       = Q . DoubleE . fromInteger
  abs (Q e)         = Q (abs e)
  signum (Q e)      = Q (signum e)

instance Fractional (Q Double) where
  (/) (Q e1) (Q e2) = Q (e1 / e2)
  fromRational = Q . DoubleE . fromRational

-- * Support for View Patterns

class (ToView a ~ b, FromView b ~ a) => View a b where
  type ToView a
  type FromView b
  view :: a -> b
  fromView :: b -> a

tuple :: (View a b) => b -> a
tuple = fromView

record :: (View a b) => b -> a
record = fromView

instance View (Q ()) (Q ()) where
  type ToView (Q ()) = Q ()
  type FromView (Q ()) = Q ()
  view = id
  fromView = id

instance View (Q Bool) (Q Bool) where
  type ToView (Q Bool) = Q Bool
  type FromView (Q Bool) = Q Bool
  view = id
  fromView = id

instance View (Q Char) (Q Char) where
  type ToView (Q Char) = Q Char
  type FromView (Q Char) = Q Char
  view = id
  fromView = id

instance View (Q Integer) (Q Integer) where
  type ToView (Q Integer) = Q Integer
  type FromView (Q Integer) = Q Integer
  view = id
  fromView = id

instance View (Q Double) (Q Double) where
  type ToView (Q Double) = Q Double
  type FromView (Q Double) = Q Double
  view = id
  fromView = id

instance View (Q Text) (Q Text) where
  type ToView (Q Text) = Q Text
  type FromView (Q Text) = Q Text
  view = id
  fromView = id

instance (QA a, QA b) => View (Q (a,b)) (Q a,Q b) where
  type ToView (Q (a,b)) = (Q a,Q b)
  type FromView (Q a,Q b) = (Q (a,b))
  view (Q e) = (Q (AppE Fst e),Q (AppE Snd e))
  fromView (Q a,Q b) = Q (PairE a b)

instance IsString (Q Text) where
  fromString = Q . TextE . T.pack