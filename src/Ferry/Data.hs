module Ferry.Data where

import Ferry.Impossible

import Data.Convertible
import Data.Typeable
import Database.HDBC
import Data.ByteString.Char8 (unpack)

data Exp =
    UnitE
  | BoolE Bool
  | CharE Char
  | IntegerE Integer
  | DoubleE Double
  | TupleE Exp Exp
  | ListE [Exp]
  | LamE (Exp -> Exp)
  | AppE (Exp -> Exp) Exp
  | AppE1 Fun1 Exp
  | AppE2 Fun2 Exp Exp
  | AppE3 Fun3 Exp Exp Exp
  | TableE String
  | VarE Int
  | Exp ::: Type

data Fun1 =
    Fst | Snd | Not | Abs | Signum
  | Negate | Head | Tail | Unzip | Minimum
  | Maximum | Concat | Product | Sum | And
  | Or | Reverse | Length | Null | Init
  | Last | The | Nub
  deriving (Eq,Show)


data Fun2 =
    Add | Mul | All | Any | Index
  | SortWith | Cons | Snoc | Take | Drop
  | Map | Append | Filter | GroupWith | Zip
  | Elem | Break | Span | DropWhile | TakeWhile
  | SplitAt | Replicate | Equ | Conj | Disj
  | Lt | Lte | Gte | Gt
  deriving (Eq,Show)

data Fun3 = Cond | ZipWith
  deriving (Eq,Show)


data Norm =
    UnitN
  | BoolN Bool
  | CharN Char
  | IntegerN Integer
  | DoubleN Double
  | TupleN Norm Norm
  | ListN [Norm]
  deriving (Eq,Ord,Show, Typeable)

data Type =
    UnitT
  | BoolT
  | CharT
  | IntegerT
  | DoubleT
  | TupleT Type Type
  | ListT Type
  | ArrowT Type Type
  deriving (Eq, Show, Typeable)

data Q a = Q Exp

class QA a where
  reify :: a -> Type
  toNorm :: a -> Norm
  fromNorm :: Norm -> a

instance QA () where
  reify _ = UnitT
  toNorm _ = UnitN
  fromNorm (UnitN) = ()
  fromNorm _ = $impossible

instance QA Bool where
  reify _ = BoolT
  toNorm b = BoolN b
  fromNorm (BoolN b) = b
  fromNorm _ = $impossible

instance QA Char where
  reify _ = CharT
  toNorm c = CharN c
  fromNorm (CharN c) = c
  fromNorm _ = $impossible

instance QA Integer where
  reify _ = IntegerT
  toNorm i = IntegerN i
  fromNorm (IntegerN i) = i
  fromNorm _ = $impossible

instance QA Double where
  reify _ = DoubleT
  toNorm d = DoubleN d
  fromNorm (DoubleN i) = i
  fromNorm _ = $impossible

instance (QA a,QA b) => QA (a,b) where
  reify _ = TupleT (reify (undefined :: a)) (reify (undefined :: b))
  toNorm (a,b) = TupleN (toNorm a) (toNorm b)
  fromNorm (TupleN a b) = (fromNorm a,fromNorm b)
  fromNorm _ = $impossible

instance (QA a) => QA [a] where
  reify _ = ListT (reify (undefined :: a))
  toNorm as = ListN (map toNorm as)
  fromNorm (ListN as) = map fromNorm as
  fromNorm _ = $impossible

class BasicType a where

instance BasicType () where
instance BasicType Bool where
instance BasicType Char where
instance BasicType Integer where
instance BasicType Double where
instance BasicType String where

-- * Refering to Real Database Tables

class (QA a) => TA a where
  table :: String -> Q [a]
  table s = Q (TableE s ::: (reify (undefined :: [a])))

instance TA () where
instance TA Bool where
instance TA Char where
instance TA Integer where
instance TA Double where
instance (BasicType a, BasicType b, QA a, QA b) => TA (a,b) where

-- * Eq, Ord, Show and Num Instances for Databse Queries

instance Show (Q a) where
  show _ = "Query"

instance Eq (Q Integer) where
  (==) _ _ = undefined

instance Eq (Q Double) where
  (==) _ _ = undefined

instance Num (Q Integer) where
  (+) (Q e1) (Q e2) = Q (AppE2 Add e1 e2       ::: reify (undefined :: Integer))
  (*) (Q e1) (Q e2) = Q (AppE2 Mul e1 e2       ::: reify (undefined :: Integer))
  abs (Q e1)        = Q (AppE1 Abs e1          ::: reify (undefined :: Integer))
  negate (Q e1)     = Q (AppE1 Negate e1       ::: reify (undefined :: Integer))
  fromInteger i     = Q (IntegerE i            ::: reify (undefined :: Integer))
  signum (Q e1)     = Q (AppE1 Signum e1       ::: reify (undefined :: Integer))

instance Num (Q Double) where
  (+) (Q e1) (Q e2) = Q (AppE2 Add e1 e2          ::: reify (undefined :: Double))
  (*) (Q e1) (Q e2) = Q (AppE2 Mul e1 e2          ::: reify (undefined :: Double))
  abs (Q e1)        = Q (AppE1 Abs e1             ::: reify (undefined :: Double))
  negate (Q e1)     = Q (AppE1 Negate e1          ::: reify (undefined :: Double))
  fromInteger d     = Q (DoubleE (fromIntegral d) ::: reify (undefined :: Double))
  signum (Q e1)     = Q (AppE1 Signum e1          ::: reify (undefined :: Double))



-- * Support for View Patterns

class View a b | a -> b, b -> a where
  view :: a -> b
  fromView :: b -> a

instance View (Q ()) (Q ()) where
  view = id
  fromView = id

instance View (Q Bool) (Q Bool) where
  view = id
  fromView = id

instance View (Q Char) (Q Char) where
  view = id
  fromView = id

instance View (Q Integer) (Q Integer) where
  view = id
  fromView = id

instance View (Q Double) (Q Double) where
  view = id
  fromView = id

instance (QA a,QA b) => View (Q (a,b)) (Q a, Q b) where
  view (Q a) = (Q (AppE1 Fst a), Q (AppE1 Snd a))
  fromView ((Q e1),(Q e2)) = Q (TupleE e1 e2)

instance Convertible Norm Exp where
    safeConvert n = Right $
        case n of
             UnitN          -> UnitE
             BoolN  b       -> BoolE b
             CharN c        -> CharE c
             IntegerN i     -> IntegerE i
             DoubleN d      -> DoubleE d
             TupleN n1 n2   -> TupleE (convert n1) (convert n2)
             ListN ns       -> ListE (map convert ns)

forget :: (QA a) => Q a -> Exp
forget (Q a) = a

toLam1 :: forall a b. (QA a,QA b) => (Q a -> Q b) -> Exp
toLam1 f = LamE (forget . f . Q) ::: ArrowT (reify (undefined :: a)) (reify (undefined :: b))

toLam2 :: forall a b c. (QA a,QA b,QA c) => (Q a -> Q b -> Q c) -> Exp
toLam2 f =
  let f1 = \a b -> forget (f (Q a) (Q b))
      t1 = ArrowT (reify (undefined :: b)) (reify (undefined :: c))
      f2 = \a -> LamE (\b -> f1 a b) ::: t1
      t2 = ArrowT (reify (undefined :: a)) t2
  in  LamE f2 ::: t2

unfoldType :: Type -> [Type]
unfoldType (TupleT t1 t2) = t1 : unfoldType t2
unfoldType t = [t]

instance Convertible Type SqlTypeId where
    safeConvert n =
        case n of
             IntegerT       -> Right SqlBigIntT
             DoubleT        -> Right SqlDoubleT
             BoolT          -> Right SqlBitT
             CharT          -> Right SqlCharT
             ListT CharT    -> Right SqlVarCharT
             UnitT          -> convError "No `UnitT' representation" n
             TupleT {}      -> convError "No `TupleT' representation" n
             ListT {}       -> convError "No `ListT' representation" n
             ArrowT {}      -> convError "No `ArrowT' representation" n

instance Convertible SqlTypeId Type where
    safeConvert n =
        case n of
             SqlBigIntT         -> Right IntegerT
             SqlDoubleT         -> Right DoubleT
             SqlBitT            -> Right BoolT
             SqlCharT           -> Right CharT
             SqlVarCharT        -> Right (ListT CharT)
             _                  -> convError "Unsupported `SqlTypeId'" n


instance Convertible SqlValue Norm where
    safeConvert sql =
        case sql of
             SqlNull            -> Right $ UnitN
             SqlInteger i       -> Right $ IntegerN i
             SqlDouble d        -> Right $ DoubleN d
             SqlBool b          -> Right $ BoolN b
             SqlChar c          -> Right $ CharN c
             SqlByteString s    -> Right $ ListN (map CharN $ unpack s)
             _                  -> convError "Unsupported `SqlValue'" sql

instance Convertible Norm SqlValue where
    safeConvert n =
        case n of
             UnitN                  -> Right $ SqlNull
             IntegerN i             -> Right $ SqlInteger i
             DoubleN d              -> Right $ SqlDouble d
             BoolN b                -> Right $ SqlBool b
             CharN c                -> Right $ SqlChar c
             ListN []               -> Right $ SqlString []
             ListN (CharN c : s)    -> case safeConvert (ListN s) of
                                            Right (SqlString s') -> Right (SqlString $ c : s')
                                            _                    -> convError "Only lists of `CharN' can be converted to `SqlString'" n
             ListN _                -> convError "Cannot convert `Norm' to `SqlValue'" n
             TupleN _ _             -> convError "Cannot convert `Norm' to `SqlValue'" n