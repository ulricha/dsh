{-# LANGUAGE TemplateHaskell, ViewPatterns, ScopedTypeVariables, MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances, DeriveDataTypeable #-}

module Database.DSH.Data where

import Database.DSH.Impossible

import Data.Convertible
import Data.Typeable
import Database.HDBC
import Data.Generics
import Data.Text(Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as T

-- import Data.Time
import GHC.Exts

type Time = Integer
type Real = Double

data Exp =
    UnitE Type
  | BoolE Bool Type
  | CharE Char Type
  | IntegerE Integer Type
  | DoubleE Double Type
  | TextE Text Type
  | TimeE Time Type
  | TupleE Exp Exp Type
  | ListE [Exp] Type
  | LamE (Exp -> Exp) Type
  | AppE (Exp -> Exp) Exp Type
  | AppE1 Fun1 Exp Type
  | AppE2 Fun2 Exp Exp Type
  | AppE3 Fun3 Exp Exp Exp Type
  | TableE Table Type
  | VarE Int Type
   deriving (Data, Typeable)

data Fun1 =
    Fst | Snd | Not | IntegerToDouble
  | Head | Tail | Unzip | Minimum
  | Maximum | Concat | Sum | And
  | Or | Reverse | Length | Null | Init
  | Last | The | Nub
  deriving (Eq, Ord, Show, Data, Typeable)


data Fun2 =
    Add | Mul | Sub | Div | All | Any | Index
  | SortWith | Cons | Snoc | Take | Drop
  | Map | Append | Filter | GroupWith | Zip
  | Elem | Break | Span | DropWhile | TakeWhile
  | SplitAt | Equ | Conj | Disj
  | Lt | Lte | Gte | Gt | Max | Min
  deriving (Eq, Ord, Show, Data, Typeable)

data Fun3 = Cond | ZipWith
  deriving (Eq, Ord, Show, Data, Typeable)


data Norm =
    UnitN Type
  | BoolN Bool Type
  | CharN Char Type
  | IntegerN Integer Type
  | DoubleN Double Type
  | TextN Text Type
  | TimeN Time Type
  | TupleN Norm Norm Type
  | ListN [Norm] Type
  deriving (Eq, Ord, Show, Data, Typeable)

data Type =
    UnitT
  | BoolT
  | CharT
  | IntegerT
  | DoubleT
  | TextT
  | TimeT
  | TupleT Type Type
  | ListT Type
  | ArrowT Type Type
  deriving (Eq, Ord, Show, Data, Typeable)


data Table =
    TableDB   String [[String]]
  | TableCSV  String
  deriving (Eq, Ord, Show, Data, Typeable)
  
  
typeExp :: Exp -> Type
typeExp e = case e of
  UnitE t -> t
  BoolE _ t -> t
  CharE _ t -> t
  IntegerE _ t -> t
  DoubleE _ t -> t
  TextE _ t -> t
  TimeE _ t -> t
  TupleE _ _ t -> t
  ListE _ t -> t
  LamE _ t -> t
  AppE _ _ t -> t
  AppE1 _ _ t -> t
  AppE2 _ _ _ t -> t
  AppE3 _ _ _ _ t -> t
  TableE _ t -> t
  VarE _ t -> t

typeArrowResult :: Type -> Type
typeArrowResult (ArrowT _ t) = t
typeArrowResult _ = $impossible

typeTupleFst :: Type -> Type
typeTupleFst (TupleT a _) = a
typeTupleFst _ = $impossible

typeTupleSnd :: Type -> Type
typeTupleSnd (TupleT _ b) = b
typeTupleSnd _ = $impossible

typeNorm :: Norm -> Type
typeNorm = typeExp . convert

data Q a = Q Exp

class QA a where
  reify :: a -> Type
  toNorm :: a -> Norm
  fromNorm :: Norm -> a

instance QA () where
  reify _ = UnitT
  toNorm _ = UnitN UnitT
  fromNorm (UnitN UnitT) = ()
  fromNorm _ = $impossible

instance QA Bool where
  reify _ = BoolT
  toNorm b = BoolN b BoolT
  fromNorm (BoolN b BoolT) = b
  fromNorm v = $impossible

instance QA Char where
  reify _ = CharT
  toNorm c = CharN c CharT
  fromNorm (CharN c CharT) = c
  fromNorm _ = $impossible

instance QA Integer where
  reify _ = IntegerT
  toNorm i = IntegerN i IntegerT
  fromNorm (IntegerN i IntegerT) = i
  fromNorm _ = $impossible

instance QA Double where
  reify _ = DoubleT
  toNorm d = DoubleN d DoubleT
  fromNorm (DoubleN i DoubleT) = i
  fromNorm _ = $impossible

instance QA Text where
    reify _ = TextT
    toNorm t = TextN t TextT
    fromNorm (TextN t TextT) = t
    fromNorm _ = $impossible

-- instance QA Time where
--     reify _ = TimeT
--     toNorm t = TimeN t TimeT
--     fromNorm (TimeN t TimeT) = t
--     fromNorm _ = $impossible


instance (QA a,QA b) => QA (a,b) where
  reify _ = TupleT (reify (undefined :: a)) (reify (undefined :: b))
  toNorm (a,b) = TupleN (toNorm a) (toNorm b) (reify (a,b))
  fromNorm (TupleN a b (TupleT _ _)) = (fromNorm a,fromNorm b)
  fromNorm _ = $impossible

instance (QA a) => QA [a] where
  reify _ = ListT (reify (undefined :: a))
  toNorm as = ListN (map toNorm as) (reify as)
  fromNorm (ListN as (ListT _)) = map fromNorm as
  fromNorm _ = $impossible

class BasicType a where

instance BasicType () where
instance BasicType Bool where
instance BasicType Char where
instance BasicType Integer where
instance BasicType Double where
instance BasicType Text where
-- instance BasicType Time where

-- * Refering to Real Database Tables

class (QA a) => TA a where
  tablePersistence :: Table -> Q [a]
  tablePersistence t = Q (TableE t (reify (undefined :: [a])))


table :: (TA a) => String -> Q [a]
table = tableDB

tableDB :: (TA a) => String -> Q [a]
tableDB name = tablePersistence (TableDB name [])

tableWithKeys :: (TA a) => String -> [[String]] -> Q [a]
tableWithKeys name keys = tablePersistence (TableDB name keys)

tableCSV :: (TA a) => String -> Q [a]
tableCSV filename = tablePersistence (TableCSV filename)


instance TA () where
instance TA Bool where
instance TA Char where
instance TA Integer where
instance TA Double where
instance TA Text where
instance (BasicType a, BasicType b, QA a, QA b) => TA (a,b) where

-- * Eq, Ord, Show and Num Instances for Databse Queries

instance Show (Q a) where
  show _ = "Query"

instance Eq (Q Integer) where
  (==) _ _ = error "Eq instance for (Q Integer) must not be used."

instance Eq (Q Double) where
  (==) _ _ = error "Eq instance for (Q Double) must not be used."

instance Num (Q Integer) where
  (+) (Q e1) (Q e2) = Q (AppE2 Add e1 e2 IntegerT)
  (*) (Q e1) (Q e2) = Q (AppE2 Mul e1 e2 IntegerT)
  (-) (Q e1) (Q e2) = Q (AppE2 Sub e1 e2 IntegerT)

  fromInteger i = Q (IntegerE i      IntegerT)

  abs (Q e1) =
    let zero      = IntegerE 0 IntegerT
        e1Negated = AppE2 Sub zero e1 IntegerT
    in Q (AppE3 Cond (AppE2 Lt e1 zero BoolT) e1Negated e1 IntegerT)

  signum (Q e1) =
    let zero     = IntegerE 0 IntegerT
        one      = IntegerE 1 IntegerT
        minusOne = IntegerE (negate 1) IntegerT
    in Q (AppE3 Cond (AppE2 Lt e1 zero BoolT)
                     (minusOne)
                     (AppE3 Cond (AppE2 Equ e1 zero BoolT) zero one IntegerT)
                     IntegerT)

instance Num (Q Double) where
  (+) (Q e1) (Q e2) = Q (AppE2 Add e1 e2 DoubleT)
  (*) (Q e1) (Q e2) = Q (AppE2 Mul e1 e2 DoubleT)
  (-) (Q e1) (Q e2) = Q (AppE2 Sub e1 e2 DoubleT)

  fromInteger d     = Q (DoubleE (fromIntegral d) DoubleT)

  abs (Q e1) =
    let zero      = DoubleE 0.0 DoubleT
        e1Negated = AppE2 Sub zero e1 DoubleT
    in Q (AppE3 Cond (AppE2 Lt e1 zero BoolT) e1Negated e1 DoubleT)

  signum (Q e1) =
    let zero     = DoubleE 0.0 DoubleT
        one      = DoubleE 1.0 DoubleT
        minusOne = DoubleE (negate 1.0) DoubleT
    in Q (AppE3 Cond (AppE2 Lt e1 zero BoolT)
                     (minusOne)
                     (AppE3 Cond (AppE2 Equ e1 zero BoolT) zero one DoubleT)
                     DoubleT)


instance Fractional (Q Double) where
  (/) (Q e1) (Q e2) = Q (AppE2 Div e1 e2          DoubleT)
  fromRational r    = Q (DoubleE (fromRational r) DoubleT)

-- * Support for View Patterns

class View a b | a -> b, b -> a where
  view :: a -> b
  fromView :: b -> a

tuple :: (View a b) => b -> a
tuple = fromView

record :: (View a b) => b -> a
record = fromView

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

instance View (Q Text) (Q Text) where
  view = id
  fromView = id

-- instance View (Q Time) (Q Time) where
--   view = id
--   fromView = id

instance (QA a,QA b) => View (Q (a,b)) (Q a, Q b) where
  view (Q a) = (Q (AppE1 Fst a (reify (undefined :: a))), Q (AppE1 Snd a (reify (undefined :: b))))
  fromView ((Q e1),(Q e2)) = Q (TupleE e1 e2 (reify (undefined :: (a, b))))

instance Convertible Norm Exp where
    safeConvert n = Right $
        case n of
             UnitN t        -> UnitE t
             BoolN b t      -> BoolE b t
             CharN c t      -> CharE c t
             TextN s t      -> TextE s t
             TimeN u t      -> TimeE u t
             IntegerN i t   -> IntegerE i t
             DoubleN d t    -> DoubleE d t
             TupleN n1 n2 t -> TupleE (convert n1) (convert n2) t
             ListN ns t     -> ListE (map convert ns) t

forget :: (QA a) => Q a -> Exp
forget (Q a) = a

toLam1 :: forall a b. (QA a,QA b) => (Q a -> Q b) -> Exp
toLam1 f = LamE (forget . f . Q) (ArrowT (reify (undefined :: a)) (reify (undefined :: b)))

toLam2 :: forall a b c. (QA a,QA b,QA c) => (Q a -> Q b -> Q c) -> Exp
toLam2 f =
  let f1 = \a b -> forget (f (Q a) (Q b))
      t1 = ArrowT (reify (undefined :: b)) (reify (undefined :: c))
      f2 = \a -> LamE (\b -> f1 a b) t1
      t2 = ArrowT (reify (undefined :: a)) t1
  in  LamE f2 t2

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
             TextT          -> Right SqlVarCharT
             TimeT          -> Right SqlTimestampT
             UnitT          -> convError "No `UnitT' representation" n
             TupleT {}      -> convError "No `TupleT' representation" n
             ListT {}       -> convError "No `ListT' representation" n
             ArrowT {}      -> convError "No `ArrowT' representation" n

instance Convertible SqlTypeId Type where
    safeConvert n =
        case n of
             SqlBigIntT         -> Right IntegerT
             SqlDoubleT         -> Right DoubleT
             SqlRealT           -> Right DoubleT
             SqlBitT            -> Right BoolT
             SqlCharT           -> Right CharT
             SqlVarCharT        -> Right TextT
             SqlDateT           -> Right TimeT
             SqlTimestampT      -> Right TimeT
             _                  -> convError "Unsupported `SqlTypeId'" n


instance Convertible SqlValue Norm where
    safeConvert sql =
        case sql of
             SqlNull            -> Right $ UnitN UnitT
             SqlInteger i       -> Right $ IntegerN i IntegerT
             SqlDouble d        -> Right $ DoubleN d DoubleT
             SqlBool b          -> Right $ BoolN b BoolT
             SqlChar c          -> Right $ CharN c CharT
             SqlString t        -> Right $ TextN (T.pack t) TextT
             SqlByteString s    -> Right $ TextN (T.decodeUtf8 s) TextT
             -- SqlLocalTime t     -> Right $ TimeN (localTimeToUTC utc t) TimeT
             -- SqlLocalDate d     -> Right $ TimeN (UTCTime d 0) TimeT
             _                  -> convError "Unsupported `SqlValue'" sql

instance Convertible (SqlValue, Type) Norm where
    safeConvert sql =
        case sql of
          (SqlNull, UnitT)         -> Right $ UnitN UnitT

          (SqlInteger i, IntegerT) -> Right $ IntegerN i IntegerT
          (SqlInt32 i, IntegerT)   -> Right $ flip IntegerN IntegerT $ convert i
          (SqlInt64 i, IntegerT)   -> Right $ flip IntegerN IntegerT $ convert i
          (SqlWord32 i, IntegerT)  -> Right $ flip IntegerN IntegerT $ convert i
          (SqlWord64 i, IntegerT)  -> Right $ flip IntegerN IntegerT $ convert i

          (SqlDouble d, DoubleT)   -> Right $ DoubleN d DoubleT
          (SqlRational r, DoubleT) -> Right $ flip DoubleN DoubleT $ convert r
          (SqlInteger i, DoubleT)  -> Right $ flip DoubleN DoubleT $ convert i
          (SqlInt32 i, DoubleT)    -> Right $ flip DoubleN DoubleT $ convert i
          (SqlInt64 i, DoubleT)    -> Right $ flip DoubleN DoubleT $ convert i
          (SqlWord32 i, DoubleT)   -> Right $ flip DoubleN DoubleT $ convert i
          (SqlWord64 i, DoubleT)   -> Right $ flip DoubleN DoubleT $ convert i

          (SqlBool b, BoolT)       -> Right $ BoolN b BoolT
          (SqlInteger i, BoolT)    -> Right $ BoolN (i == 1) BoolT
          (SqlInt32 i, BoolT)      -> Right $ BoolN (i == 1) BoolT
          (SqlInt64 i, BoolT)      -> Right $ BoolN (i == 1) BoolT
          (SqlWord32 i, BoolT)     -> Right $ BoolN (i == 1) BoolT
          (SqlWord64 i, BoolT)     -> Right $ BoolN (i == 1) BoolT

          (SqlString s, TextT)     -> Right $ TextN (T.pack s) TextT
          (SqlByteString s, TextT) -> Right $ TextN (T.decodeUtf8 s) TextT

          (SqlChar c, CharT) -> Right $ CharN c CharT
          (SqlString (c : _), CharT) -> Right $ CharN c CharT
          (SqlByteString ((T.unpack . T.decodeUtf8) -> (c : _)), CharT)  -> Right $ CharN c CharT

          _                        -> error (show sql) -- $impossible

instance Convertible Norm SqlValue where
    safeConvert n =
        case n of
             UnitN _             -> Right $ SqlNull
             IntegerN i _        -> Right $ SqlInteger i
             DoubleN d _         -> Right $ SqlDouble d
             BoolN b _           -> Right $ SqlBool b
             CharN c _           -> Right $ SqlChar c
             TextN t _           -> Right $ SqlString $ T.unpack t
             TimeN _t _          -> convError "Cannot convert `Norm' to `SqlValue'" n -- Right $ SqlUTCTime t
             ListN _ _           -> convError "Cannot convert `Norm' to `SqlValue'" n
             TupleN _ _ _        -> convError "Cannot convert `Norm' to `SqlValue'" n
                        
                        
instance IsString (Q Text) where
  fromString s = Q (TextE (T.pack s) TextT)