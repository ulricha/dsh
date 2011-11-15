{-# LANGUAGE GADTs, TemplateHaskell, ViewPatterns, ScopedTypeVariables, MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances, DeriveDataTypeable #-}

module Database.DSH.Data where

import Database.DSH.Impossible

import Data.Convertible
import Data.Typeable
import Database.HDBC
import Data.Generics
import Data.Text(Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as T

import GHC.Exts

data Exp =
    UnitE Type
  | BoolE Bool Type
  | CharE Char Type
  | IntegerE Integer Type
  | DoubleE Double Type
  | TextE Text Type
  | TupleE Exp Exp Type
  | ListE [Exp] Type
  | LamE (Exp -> Exp) Type
  | AppE1 Fun1 Exp Type
  | AppE2 Fun2 Exp Exp Type
  | AppE3 Fun3 Exp Exp Exp Type
  | TableE Table Type
  | VarE Int Type
   deriving (Show, Data, Typeable)

instance Show (Exp -> Exp) where
  show _ = "(f :: Exp -> Exp)"

data Q a where
  ToQ               :: (QA a)               =>  a -> Q a
  PairQ             :: (QA a,QA b)          =>  Q a -> Q b -> Q (a,b)
  TableQ            :: (TA a)               =>  Table -> Q [a]
  FstQ              :: (QA a,QA b)          =>  Q (a,b) -> Q a
  SndQ              :: (QA a,QA b)          =>  Q (a,b) -> Q b
  NotQ              ::                          Q Bool -> Q Bool
  IntegerToDoubleQ  ::                          Q Integer -> Q Double
  HeadQ             :: (QA a)               =>  Q [a] -> Q a
  TailQ             :: (QA a)               =>  Q [a] -> Q [a]
  UnzipQ            :: (QA a,QA b)          =>  Q [(a,b)] -> Q ([a],[b])
  MinimumQ          :: (QA a,Ord a)         =>  Q [a] -> Q a
  MaximumQ          :: (QA a,Ord a)         =>  Q [a] -> Q a
  ConcatQ           :: (QA a)               =>  Q [[a]] -> Q [a]
  SumQ              :: (QA a,Num a)         =>  Q [a] -> Q a
  AndQ              ::                          Q [Bool] -> Q Bool
  OrQ               ::                          Q [Bool] -> Q Bool
  ReverseQ          :: (QA a)               =>  Q [a] -> Q [a]
  LengthQ           :: (QA a)               =>  Q [a] -> Q Integer
  NullQ             :: (QA a)               =>  Q [a] -> Q Bool
  InitQ             :: (QA a)               =>  Q [a] -> Q [a]
  LastQ             :: (QA a)               =>  Q [a] -> Q a
  TheQ              :: (QA a,Eq a)          =>  Q [a] -> Q a
  NubQ              :: (QA a,Eq a)          =>  Q [a] -> Q [a]
  AddQ              :: (QA a,Num a)         =>  Q a -> Q a -> Q a
  MulQ              :: (QA a,Num a)         =>  Q a -> Q a -> Q a
  SubQ              :: (QA a,Num a)         =>  Q a -> Q a -> Q a
  DivQ              :: (QA a,Fractional a)  =>  Q a -> Q a -> Q a
  AllQ              :: (QA a)               =>  (Q a -> Q Bool) -> Q [a] -> Q Bool
  AnyQ              :: (QA a)               =>  (Q a -> Q Bool) -> Q [a] -> Q Bool
  IndexQ            :: (QA a)               =>  Q [a] -> Q Integer -> Q a
  SortWithQ         :: (QA a,QA b,Ord b)    =>  (Q a -> Q b) -> Q [a] -> Q [a]
  ConsQ             :: (QA a)               =>  Q a -> Q [a] -> Q [a]
  SnocQ             :: (QA a)               =>  Q [a] -> Q a -> Q [a]
  TakeQ             :: (QA a)               =>  Q Integer -> Q [a] -> Q [a]
  DropQ             :: (QA a)               =>  Q Integer -> Q [a] -> Q [a]
  MapQ              :: (QA a,QA b)          =>  (Q a -> Q b) -> Q [a] -> Q [b]
  AppendQ           :: (QA a)               =>  Q [a] -> Q [a] -> Q [a]
  FilterQ           :: (QA a)               =>  (Q a -> Q Bool) -> Q [a] -> Q [a]
  GroupWithQ        :: (QA a,QA b,Ord b)    =>  (Q a -> Q b) -> Q [a] -> Q [[a]]
  ZipQ              :: (QA a,QA b)          =>  Q [a] -> Q [b] -> Q [(a,b)]
  BreakQ            :: (QA a)               =>  (Q a -> Q Bool) -> Q [a] -> Q ([a], [a])
  SpanQ             :: (QA a)               =>  (Q a -> Q Bool) -> Q [a] -> Q ([a], [a])
  DropWhileQ        :: (QA a)               =>  (Q a -> Q Bool) -> Q [a] -> Q [a]
  TakeWhileQ        :: (QA a)               =>  (Q a -> Q Bool) -> Q [a] -> Q [a]
  SplitAtQ          :: (QA a)               =>  Q Integer -> Q [a] -> Q ([a],[a])
  EquQ              :: (QA a,Eq a)          =>  Q a -> Q a -> Q Bool
  ConjQ             ::                          Q Bool -> Q Bool -> Q Bool
  DisjQ             ::                          Q Bool -> Q Bool -> Q Bool
  LtQ               :: (QA a,Ord a)         => Q a -> Q a -> Q Bool
  LteQ              :: (QA a,Ord a)         => Q a -> Q a -> Q Bool
  GteQ              :: (QA a,Ord a)         => Q a -> Q a -> Q Bool
  GtQ               :: (QA a,Ord a)         => Q a -> Q a -> Q Bool
  MaxQ              :: (QA a,Ord a)         => Q a -> Q a -> Q a
  MinQ              :: (QA a,Ord a)         => Q a -> Q a -> Q a
  CondQ             :: (QA a)               => Q Bool -> Q a -> Q a -> Q a
  ZipWithQ          :: (QA a,QA b,QA c)     => (Q a -> Q b -> Q c) -> Q [a] -> Q [b] -> Q [c]
  UntypedQ          :: (QA a)               => Exp -> Q a

instance Show (Q a) where
  show _ = "(Q a)"

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
  | Break | Span | DropWhile | TakeWhile
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
  UnitE t         -> t
  BoolE _ t       -> t
  CharE _ t       -> t
  IntegerE _ t    -> t
  DoubleE _ t     -> t
  TextE _ t       -> t
  TupleE _ _ t    -> t
  ListE _ t       -> t
  LamE _ t        -> t
  AppE1 _ _ t     -> t
  AppE2 _ _ _ t   -> t
  AppE3 _ _ _ _ t -> t
  TableE _ t      -> t
  VarE _ t        -> t

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

unfoldType :: Type -> [Type]
unfoldType (TupleT t1 t2) = t1 : unfoldType t2
unfoldType t = [t]

-- data Q a = Q Exp deriving (Show, Data, Typeable)

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

-- * Refering to Real Database Tables

class (QA a) => TA a where
  tablePersistence :: Table -> Q [a]
  tablePersistence t = TableQ t


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

-- * Eq, Ord and Num Instances for Databse Queries

instance Eq (Q Integer) where
  (==) _ _ = error "Eq instance for (Q Integer) must not be used."

instance Eq (Q Double) where
  (==) _ _ = error "Eq instance for (Q Double) must not be used."

instance Num (Q Integer) where
  (+)         = AddQ
  (*)         = MulQ
  (-)         = SubQ
  fromInteger = ToQ
  abs e       = CondQ (LtQ e 0) (negate e) e
  signum e    = CondQ (LtQ e 0) (-1) (CondQ (EquQ e 0) 0 1)

instance Num (Q Double) where
  (+)         = AddQ
  (*)         = MulQ
  (-)         = SubQ
  fromInteger = ToQ . fromInteger
  abs e       = CondQ (LtQ e 0) (negate e) e
  signum e    = CondQ (LtQ e 0) (-1) (CondQ (EquQ e 0) 0 1)

instance Fractional (Q Double) where
  (/)           = DivQ
  fromRational  = ToQ . fromRational

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

instance (QA a,QA b) => View (Q (a,b)) (Q a, Q b) where
  view e = (FstQ e, SndQ e)
  fromView (e1,e2) = PairQ e1 e2

instance Convertible Norm Exp where
    safeConvert n = Right $
        case n of
             UnitN t        -> UnitE t
             BoolN b t      -> BoolE b t
             CharN c t      -> CharE c t
             TextN s t      -> TextE s t
             IntegerN i t   -> IntegerE i t
             DoubleN d t    -> DoubleE d t
             TupleN n1 n2 t -> TupleE (convert n1) (convert n2) t
             ListN ns t     -> ListE (map convert ns) t

instance (QA a) => Convertible (Q a) Exp where
  safeConvert q =
    let rt = reify (undefined :: a)
    in  Right $ case q of
                  UntypedQ e          -> e
                  ToQ a               -> convert (toNorm a)
                  TableQ t            -> TableE                 t                                       rt
                  FstQ e              -> AppE1 Fst              (convert e)                             rt
                  SndQ e              -> AppE1 Snd              (convert e)                             rt
                  NotQ e              -> AppE1 Not              (convert e)                             rt
                  IntegerToDoubleQ e  -> AppE1 IntegerToDouble  (convert e)                             rt
                  HeadQ e             -> AppE1 Head             (convert e)                             rt
                  TailQ e             -> AppE1 Tail             (convert e)                             rt
                  UnzipQ e            -> AppE1 Unzip            (convert e)                             rt
                  MinimumQ e          -> AppE1 Minimum          (convert e)                             rt
                  MaximumQ e          -> AppE1 Maximum          (convert e)                             rt
                  ConcatQ e           -> AppE1 Concat           (convert e)                             rt
                  SumQ e              -> AppE1 Sum              (convert e)                             rt
                  AndQ e              -> AppE1 And              (convert e)                             rt
                  OrQ e               -> AppE1 Or               (convert e)                             rt
                  ReverseQ e          -> AppE1 Reverse          (convert e)                             rt
                  LengthQ e           -> AppE1 Length           (convert e)                             rt
                  NullQ e             -> AppE1 Null             (convert e)                             rt
                  InitQ e             -> AppE1 Init             (convert e)                             rt
                  LastQ e             -> AppE1 Last             (convert e)                             rt
                  TheQ e              -> AppE1 The              (convert e)                             rt
                  NubQ e              -> AppE1 Nub              (convert e)                             rt
                  PairQ e1 e2         -> TupleE                 (convert e1)  (convert e2)              rt
                  AddQ e1 e2          -> AppE2 Add              (convert e1)  (convert e2)              rt
                  MulQ e1 e2          -> AppE2 Mul              (convert e1)  (convert e2)              rt
                  SubQ e1 e2          -> AppE2 Sub              (convert e1)  (convert e2)              rt
                  DivQ e1 e2          -> AppE2 Div              (convert e1)  (convert e2)              rt
                  IndexQ e1 e2        -> AppE2 Index            (convert e1)  (convert e2)              rt
                  ConsQ e1 e2         -> AppE2 Cons             (convert e1)  (convert e2)              rt
                  SnocQ e1 e2         -> AppE2 Snoc             (convert e1)  (convert e2)              rt
                  AppendQ e1 e2       -> AppE2 Append           (convert e1)  (convert e2)              rt
                  ZipQ e1 e2          -> AppE2 Zip              (convert e1)  (convert e2)              rt
                  TakeQ e1 e2         -> AppE2 Take             (convert e1)  (convert e2)              rt
                  DropQ e1 e2         -> AppE2 Drop             (convert e1)  (convert e2)              rt
                  SplitAtQ e1 e2      -> AppE2 SplitAt          (convert e1)  (convert e2)              rt
                  EquQ e1 e2          -> AppE2 Equ              (convert e1)  (convert e2)              rt
                  ConjQ e1 e2         -> AppE2 Conj             (convert e1)  (convert e2)              rt
                  DisjQ e1 e2         -> AppE2 Disj             (convert e1)  (convert e2)              rt
                  LtQ e1 e2           -> AppE2 Lt               (convert e1)  (convert e2)              rt
                  LteQ e1 e2          -> AppE2 Lte              (convert e1)  (convert e2)              rt
                  GteQ e1 e2          -> AppE2 Gte              (convert e1)  (convert e2)              rt
                  GtQ e1 e2           -> AppE2 Gt               (convert e1)  (convert e2)              rt  
                  MaxQ e1 e2          -> AppE2 Max              (convert e1)  (convert e2)              rt
                  MinQ e1 e2          -> AppE2 Min              (convert e1)  (convert e2)              rt  
                  MapQ f e            -> AppE2 Map              (convert f)   (convert e)               rt
                  AllQ f e            -> AppE2 All              (convert f)   (convert e)               rt
                  AnyQ f e            -> AppE2 Any              (convert f)   (convert e)               rt
                  FilterQ f e         -> AppE2 Filter           (convert f)   (convert e)               rt
                  SortWithQ f e       -> AppE2 SortWith         (convert f)   (convert e)               rt
                  GroupWithQ f e      -> AppE2 GroupWith        (convert f)   (convert e)               rt
                  BreakQ f e          -> AppE2 Break            (convert f)   (convert e)               rt
                  SpanQ f e           -> AppE2 Span             (convert f)   (convert e)               rt
                  DropWhileQ f e      -> AppE2 DropWhile        (convert f)   (convert e)               rt
                  TakeWhileQ f e      -> AppE2 TakeWhile        (convert f)   (convert e)               rt
                  CondQ c e1 e2       -> AppE3 Cond             (convert c)   (convert e1) (convert e2) rt
                  ZipWithQ f e1 e2    -> AppE3 ZipWith          (convert f)   (convert e1) (convert e2) rt

instance (QA a,QA b) => Convertible (Q a -> Q b) Exp where
  safeConvert f = Right (LamE (convert . f . UntypedQ) (ArrowT (reify (undefined :: a)) (reify (undefined :: b))))

instance (QA a,QA b,QA c) => Convertible (Q a -> Q b -> Q c) Exp where
  safeConvert f = let f1 = \a b -> convert (f (UntypedQ a) (UntypedQ b))
                      t1 = ArrowT (reify (undefined :: b)) (reify (undefined :: c))
                      f2 = \a -> LamE (\b -> f1 a b) t1
                      t2 = ArrowT (reify (undefined :: a)) t1
                  in  Right (LamE f2 t2)

instance Convertible Type SqlTypeId where
    safeConvert n =
        case n of
             IntegerT       -> Right SqlBigIntT
             DoubleT        -> Right SqlDoubleT
             BoolT          -> Right SqlBitT
             CharT          -> Right SqlCharT
             TextT          -> Right SqlVarCharT
             UnitT          -> convError "No `UnitT' representation" n
             TupleT {}      -> convError "No `TupleT' representation" n
             ListT {}       -> convError "No `ListT' representation" n
             ArrowT {}      -> convError "No `ArrowT' representation" n

instance Convertible SqlTypeId Type where
    safeConvert n =
        case n of
          SqlCharT           -> Right TextT
          SqlVarCharT        -> Right TextT
          SqlLongVarCharT    -> Right TextT
          SqlWCharT          -> Right TextT
          SqlWVarCharT       -> Right TextT
          SqlWLongVarCharT   -> Right TextT
          SqlDecimalT        -> Right DoubleT
          SqlNumericT        -> Right DoubleT
          SqlSmallIntT       -> Right IntegerT
          SqlIntegerT        -> Right IntegerT
          SqlRealT           -> Right DoubleT
          SqlFloatT          -> Right DoubleT
          SqlDoubleT         -> Right DoubleT
          SqlBitT            -> Right BoolT
          SqlBigIntT         -> Right IntegerT
          SqlTinyIntT        -> Right IntegerT
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
          (SqlRational r, IntegerT) -> Right $ flip IntegerN IntegerT $ convert r

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

          _                        -> $impossible

instance Convertible Norm SqlValue where
    safeConvert n =
        case n of
             UnitN _             -> Right $ SqlNull
             IntegerN i _        -> Right $ SqlInteger i
             DoubleN d _         -> Right $ SqlDouble d
             BoolN b _           -> Right $ SqlBool b
             CharN c _           -> Right $ SqlChar c
             TextN t _           -> Right $ SqlString $ T.unpack t
             ListN _ _           -> convError "Cannot convert `Norm' to `SqlValue'" n
             TupleN _ _ _        -> convError "Cannot convert `Norm' to `SqlValue'" n


instance IsString (Q Text) where
  fromString = ToQ . T.pack