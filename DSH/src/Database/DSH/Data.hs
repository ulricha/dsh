module Database.DSH.Data where

import Data.String
import Data.Text (Text)
import qualified Data.Text as T
import Database.DSH.Impossible

data Exp a where
  UnitE     :: Exp ()
  BoolE     :: Bool -> Exp Bool
  CharE     :: Char -> Exp Char
  IntegerE  :: Integer -> Exp Integer
  DoubleE   :: Double -> Exp Double
  TextE     :: Text -> Exp Text
  PairE     :: (Reify (Exp a),Reify (Exp b))  => Exp a -> Exp b -> Exp (Exp a,Exp b)
  ListE     :: (Reify (Exp a))                => [Exp a] -> Exp [Exp a]
  AppE      :: (Reify (Exp a),Reify (Exp b))  => Fun (Exp a) (Exp b) -> Exp a -> Exp b
  LamE      :: (Reify (Exp a),Reify (Exp b))  => (Exp a -> Exp b) -> Exp (Exp a -> Exp b)
  VarE      :: (Reify (Exp a))                => Integer -> Exp a
  TableE    :: (Reify (Exp a))                => Table -> Exp [Exp a]

data Table =
    TableDB   String [[String]]
  | TableCSV  String
  deriving (Eq, Ord, Show)

data Type a where
  UnitT     :: Type (Exp ())
  BoolT     :: Type (Exp Bool)
  CharT     :: Type (Exp Char)
  IntegerT  :: Type (Exp Integer)
  DoubleT   :: Type (Exp Double)
  TextT     :: Type (Exp Text)
  PairT     :: (Reify (Exp a),Reify (Exp b))  => Type (Exp a) -> Type (Exp b) -> Type (Exp (Exp a,Exp b))
  ListT     :: (Reify (Exp a))                => Type (Exp a) -> Type (Exp [Exp a])
  ArrowT    :: (Reify (Exp a),Reify (Exp b))  => Type (Exp a) -> Type (Exp b) -> Type (Exp (Exp a -> Exp b))

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

instance Reify (Exp ()) where
  reify _ = UnitT

instance Reify (Exp Bool) where
  reify _ = BoolT

instance Reify (Exp Char) where
  reify _ = CharT

instance Reify (Exp Integer) where
  reify _ = IntegerT

instance Reify (Exp Double) where
  reify _ = DoubleT

instance Reify (Exp Text) where
  reify _ = TextT

instance (Reify (Exp a),Reify (Exp b)) => Reify (Exp (Exp a,Exp b)) where
  reify _ = PairT (reify (undefined :: Exp a)) (reify (undefined :: Exp b))

instance (Reify (Exp a)) => Reify (Exp [Exp a]) where
  reify _ = ListT (reify (undefined :: Exp a))

instance (Reify (Exp a),Reify (Exp b)) => Reify (Exp (Exp a -> Exp b)) where
  reify _ = ArrowT (reify (undefined :: Exp a)) (reify (undefined :: Exp b))

data Fun a b where
    Fst             :: Fun (Exp (Exp a,Exp b))       (Exp a)
    Snd             :: Fun (Exp (Exp a,Exp b))       (Exp b)
    Not             :: Fun (Exp Bool)                (Exp Bool)
    Concat          :: (Reify (Exp a)) => Fun (Exp [Exp [Exp a]])       (Exp [Exp a])
    Head            :: Fun (Exp [Exp a])             (Exp a)
    Tail            :: Fun (Exp [Exp a])             (Exp [Exp a])
    The             :: Fun (Exp [Exp a])             (Exp a)
    Init            :: Fun (Exp [Exp a])             (Exp [Exp a])
    Last            :: Fun (Exp [Exp a])             (Exp a)
    Null            :: Fun (Exp [Exp a])             (Exp Bool)
    Length          :: Fun (Exp [Exp a])             (Exp Integer)
    Reverse         :: Fun (Exp [Exp a])             (Exp [Exp a])
    And             :: Fun (Exp [Exp Bool])          (Exp Bool)
    Or              :: Fun (Exp [Exp Bool])          (Exp Bool)
    Sum             :: Fun (Exp [Exp a])             (Exp a)
    Maximum         :: Fun (Exp [Exp a])             (Exp a)
    Minimum         :: Fun (Exp [Exp a])             (Exp a)
    Unzip           :: (Reify (Exp a), Reify (Exp b)) => Fun (Exp [Exp (Exp a,Exp b)]) (Exp (Exp [Exp a], Exp [Exp b]))
    Nub             :: Fun (Exp [Exp a])             (Exp [Exp a])
    IntegerToDouble :: Fun (Exp Integer)             (Exp Double)

    Add       :: Fun (Exp (Exp a,Exp a))               (Exp a)
    Mul       :: Fun (Exp (Exp a,Exp a))               (Exp a)
    Sub       :: Fun (Exp (Exp a,Exp a))               (Exp a)
    Div       :: Fun (Exp (Exp a,Exp a))               (Exp a)
    Lt        :: Fun (Exp (Exp a,Exp a))               (Exp Bool)
    Lte       :: Fun (Exp (Exp a,Exp a))               (Exp Bool)
    Equ       :: Fun (Exp (Exp a,Exp a))               (Exp Bool)
    Gte       :: Fun (Exp (Exp a,Exp a))               (Exp Bool)
    Gt        :: Fun (Exp (Exp a,Exp a))               (Exp Bool)
    Conj      :: Fun (Exp (Exp Bool,Exp Bool))         (Exp Bool)
    Disj      :: Fun (Exp (Exp Bool,Exp Bool))         (Exp Bool)
    Min       :: Fun (Exp (Exp a,Exp a))               (Exp a)
    Max       :: Fun (Exp (Exp a,Exp a))               (Exp a)
    Cons      :: Fun (Exp (Exp a,Exp [Exp a]))         (Exp [Exp a])
    Take      :: Fun (Exp (Exp Integer,Exp [Exp a]))   (Exp [Exp a])
    Drop      :: Fun (Exp (Exp Integer,Exp [Exp a]))   (Exp [Exp a])
    Index     :: Fun (Exp (Exp [Exp a],Exp Integer))   (Exp a)
    SplitAt   :: Fun (Exp (Exp Integer,Exp [Exp a]))   (Exp (Exp [Exp a], Exp [Exp a]))
    Zip       :: Fun (Exp (Exp [Exp a],Exp [Exp b]))   (Exp [Exp (Exp a,Exp b)])
                 
    Map       :: Fun (Exp (Exp (Exp a -> Exp b),Exp [Exp a]))        (Exp [Exp b])
    Filter    :: Fun (Exp (Exp (Exp a -> Exp Bool),(Exp [Exp a])))   (Exp [Exp a])
    GroupWith :: (Reify (Exp a),Reify (Exp b)) => Fun (Exp (Exp (Exp a -> Exp b),Exp [Exp a]))        (Exp [Exp [Exp a]])
    SortWith  :: Fun (Exp (Exp (Exp a -> Exp b),Exp [Exp a]))        (Exp [Exp a])
    TakeWhile :: Fun (Exp (Exp (Exp a -> Exp Bool),Exp [Exp a]))     (Exp [Exp a])
    DropWhile :: Fun (Exp (Exp (Exp a -> Exp Bool),Exp [Exp a]))     (Exp [Exp a])
    Cond      :: Fun (Exp (Exp Bool,Exp (Exp a,Exp a))) (Exp a)


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


toQ :: (QA a) => a -> Exp (Q a)
toQ = toExp

class (Reify (Exp (Q a))) => QA a where
  type Q a
  toExp :: a -> Exp (Q a)
  frExp :: Exp (Q a) -> a

instance QA () where
  type Q () = ()
  toExp _ = UnitE
  frExp UnitE = ()
  frExp _ = $impossible

instance QA Bool where
  type Q Bool = Bool
  toExp = BoolE
  frExp (BoolE b) = b
  frExp _ = $impossible

instance QA Char where
  type Q Char = Char
  toExp = CharE
  frExp (CharE c) = c
  frExp _ = $impossible

instance QA Integer where
  type Q Integer = Integer
  toExp = IntegerE
  frExp (IntegerE e) = e
  frExp _ = $impossible

instance QA Double where
  type Q Double = Double
  toExp = DoubleE
  frExp (DoubleE d) = d
  frExp _ = $impossible

instance QA Text where
  type Q Text = Text
  toExp = TextE
  frExp (TextE t) = t
  frExp _ = $impossible

instance (QA a, QA b) => QA (a,b) where
  type Q (a,b) = (Exp (Q a),Exp (Q b))
  toExp (a,b) = PairE (toExp a) (toExp b)
  frExp (PairE a b) = (frExp a,frExp b)
  frExp _ = $impossible

instance (QA a) => QA [a] where
  type Q [a] = [Exp (Q a)]
  toExp as = ListE (map toExp as)
  frExp (ListE as) = map frExp as
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

table :: (QA a, TA a) => String -> Exp [Exp (Q a)]
table name = TableE (TableDB name [])

tableDB :: (QA a, TA a) => String -> Exp [Exp (Q a)]
tableDB name = TableE (TableDB name [])

tableWithKeys :: (QA a, TA a) => String -> [[String]] -> Exp [Exp (Q a)]
tableWithKeys name keys = TableE (TableDB name keys)

tableCSV :: (QA a, TA a) => String -> Exp [Exp (Q a)]
tableCSV filename = TableE (TableCSV filename)

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
      
  signum e = let c1 = AppE Lt  (PairE e 0)
                 c2 = AppE Equ (PairE e 0)
                 e' = AppE Cond (PairE c2 (PairE 0 1))
             in  AppE Cond (PairE c1 (PairE (-1) e'))

instance Fractional (Exp Double) where
  (/) e1 e2    = AppE Div (PairE e1 e2)
  fromRational = DoubleE . fromRational

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

instance View (Exp ()) (Exp ()) where
  type ToView (Exp ()) = Exp ()
  type FromView (Exp ()) = Exp ()
  view = id
  fromView = id

instance View (Exp Bool) (Exp Bool) where
  type ToView (Exp Bool) = Exp Bool
  type FromView (Exp Bool) = Exp Bool
  view = id
  fromView = id

instance View (Exp Char) (Exp Char) where
  type ToView (Exp Char) = Exp Char
  type FromView (Exp Char) = Exp Char
  view = id
  fromView = id

instance View (Exp Integer) (Exp Integer) where
  type ToView (Exp Integer) = Exp Integer
  type FromView (Exp Integer) = Exp Integer
  view = id
  fromView = id

instance View (Exp Double) (Exp Double) where
  type ToView (Exp Double) = Exp Double
  type FromView (Exp Double) = Exp Double
  view = id
  fromView = id

instance View (Exp Text) (Exp Text) where
  type ToView (Exp Text) = Exp Text
  type FromView (Exp Text) = Exp Text
  view = id
  fromView = id

instance (Reify (Exp b), Reify (Exp a)) => View (Exp (Exp a,Exp b)) (Exp a,Exp b) where
  type ToView (Exp (Exp a,Exp b)) = (Exp a,Exp b)
  type FromView (Exp a,Exp b) = Exp (Exp a,Exp b)
  view e = (AppE Fst e,AppE Snd e)
  fromView (a,b) = PairE a b

instance IsString (Exp Text) where
  fromString = TextE . T.pack