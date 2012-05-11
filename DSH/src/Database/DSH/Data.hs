{-# LANGUAGE TemplateHaskell,
             ViewPatterns,
             ScopedTypeVariables,
             MultiParamTypeClasses,
             FunctionalDependencies,
             FlexibleInstances,
             DeriveDataTypeable,
             TypeOperators,
             DefaultSignatures,
             FlexibleContexts,
             TypeFamilies,
             UndecidableInstances,
             DeriveGeneric #-}

module Database.DSH.Data where

import Database.DSH.Impossible

import Data.Convertible
import Data.Typeable
import Database.HDBC
import Data.Generics hiding (Generic)
import Data.Text(Text)
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import Data.Maybe
import GHC.Exts
import GHC.Generics

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
  UnitE t -> t
  BoolE _ t -> t
  CharE _ t -> t
  IntegerE _ t -> t
  DoubleE _ t -> t
  TextE _ t -> t
  TupleE _ _ t -> t
  ListE _ t -> t
  LamE _ t -> t
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

data Q a = Q Exp deriving (Show, Data, Typeable)

class QA a where
  reify :: a -> Type
  toNorm :: a -> Norm
  fromNorm :: Norm -> a
  default reify :: (Generic a, GenericQA (Rep a)) => a -> Type
  reify a = genericReify False (from a)
  default toNorm :: (Generic a, GenericQA (Rep a)) => a -> Norm
  toNorm a = genericToNorm False False (from a)
  default fromNorm :: (Generic a, GenericQA (Rep a)) => Norm -> a
  fromNorm a = case genericFromNorm False a of
                 Just r  -> to r
                 Nothing -> $impossible

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

instance QA Int where
  reify _ = IntegerT
  toNorm i = IntegerN (fromIntegral i) IntegerT
  fromNorm (IntegerN i IntegerT) = fromInteger i
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

instance (QA a) => QA [a] where
  reify _ = ListT (reify (undefined :: a))
  toNorm as = ListN (map toNorm as) (reify as)
  fromNorm (ListN as (ListT _)) = map fromNorm as
  fromNorm _ = $impossible

class GenericQA a where
    genericReify    :: Bool -> a p -> Type
    genericToNorm   :: Bool -> Bool -> a p -> Norm
    genericFromNorm :: Bool -> Norm -> Maybe (a p)

instance GenericQA U1 where
    genericReify False _ = UnitT
    genericReify True  a = ListT (genericReify False a)
    genericToNorm False _    U1 = UnitN (genericReify False U1)
    genericToNorm True False U1 = ListN [genericToNorm False False U1] (genericReify True U1)
    genericToNorm True True  _  = ListN [] (genericReify True U1)
    genericFromNorm False (UnitN UnitT) = Just U1
    genericFromNorm True  (ListN [a] (ListT UnitT)) = genericFromNorm False a
    genericFromNorm _ _ = Nothing

instance (QA a) => GenericQA (K1 i a) where
    genericReify False _ = reify (undefined :: a)
    genericReify True  a = ListT (genericReify False a)
    genericToNorm False _    (K1 a) = toNorm a
    genericToNorm True False (K1 a) = toNorm [a]
    genericToNorm True True  _      = toNorm ([] :: [a])
    genericFromNorm False a = Just (K1 (fromNorm a))
    genericFromNorm True (ListN [a] _) = Just (K1 (fromNorm a))
    genericFromNorm True _ = Nothing

instance (GenericQA a) => GenericQA (M1 i c a) where
    genericReify bf _ = genericReify bf (undefined :: a ())
    genericToNorm bf1 bf2 (M1 a) = genericToNorm bf1 bf2 a
    genericFromNorm bf a = fmap M1 (genericFromNorm bf a)

instance (GenericQA a, GenericQA b) => GenericQA (a :*: b) where
    genericReify False _ = TupleT (genericReify False (undefined :: a ()))
                                  (genericReify False (undefined :: b ()))
    genericReify True  a = ListT (genericReify False a)
    genericToNorm False _    (a :*: b) = TupleN (genericToNorm False False a)
                                                (genericToNorm False False b)
                                                (genericReify False (a :*: b))
    genericToNorm True False (a :*: b) = ListN  [genericToNorm False False (a :*: b)]
                                                (genericReify True (a :*: b))
    genericToNorm True True  _         = ListN [] (genericReify True (undefined :: (a :*: b) ()))
    genericFromNorm False (TupleN a b _) = case (genericFromNorm False a,genericFromNorm False b) of
                                             (Just ra,Just rb) -> Just (ra :*: rb)
                                             _                 -> Nothing
    genericFromNorm True  (ListN [a] _)  = genericFromNorm False a
    genericFromNorm _ _                  = Nothing

instance (GenericQA a, GenericQA b) => GenericQA (a :+: b) where
    genericReify _ _ = TupleT (genericReify True (undefined :: a ()))
                              (genericReify True (undefined :: b ()))
    genericToNorm _ False (L1 a) = TupleN (genericToNorm True False a)
                                          (genericToNorm True True  (undefined :: b ()))
                                          (genericReify True (undefined :: (a :+: b) ()))
    genericToNorm _ False (R1 b) = TupleN (genericToNorm True True  (undefined :: a ()))
                                          (genericToNorm True False b)
                                          (genericReify True (undefined :: (a :+: b) ()))
    genericToNorm _ True  _      = TupleN (genericToNorm True True  (undefined :: a ()))
                                          (genericToNorm True True  (undefined :: b ()))
                                          (genericReify True (undefined :: (a :+: b) ()))
    genericFromNorm _ (TupleN l r _) = case (genericFromNorm True l,genericFromNorm True r) of
                                         (Just r1,Nothing) -> Just (L1 r1)
                                         (Nothing,Just r1) -> Just (R1 r1)
                                         _                -> Nothing
    genericFromNorm _ _              = Nothing

-- elim :: forall a r. (Case a r, GCurry (Q a -> Cases a r -> Q r)) => GCurry1 (Q a -> Cases a r -> Q r)
-- elim = gCurry ((flip caseOf) :: Q a -> Cases a r -> Q r)

class (QA a, QA r) => Case a r where
    caseOf :: Cases a r -> Q a -> Q r
    default caseOf :: (Generic a, GenericCase (Rep a) r, GCase (Rep a) r ~ Cases a r) => Cases a r -> Q a -> Q r
    caseOf f (Q e) = gcase f (Q e :: Q ((Rep a) ()))
    type Cases a r
    type Cases a r = GCase (Rep a) r

class (GenericQA a, QA r) => GenericCase a r where
    type GCase a r
    type GRep a
    type GRep' a
    type GRep' a = [GRep a]
    gcase :: GCase a r -> Q (a p) -> Q r
    -- Alt case is called from sum constructors the subtypes seem to be ordinary but in reality it is a list, this function performs the case (except for the case of sums themselves)
    galtCase :: GCase a r -> Q (a p) -> Q [r]
    galtCase f (Q a) = mapG (gcase f) (Q a :: Q [a p])

toLamG :: forall a r p. (GenericQA a, QA r) => (Q (a p) -> Q r) -> Exp
toLamG fun = LamE (forget . fun . Q) (ArrowT (genericReify False (undefined :: (a p))) (reify (undefined :: r)))

mapG :: forall a r p. (GenericQA a, QA r) => (Q (a p) -> Q r) -> Q [(a p)] -> Q [r]
mapG f (Q arg) = Q $ AppE2 Map (toLamG f) arg (reify (undefined :: [r]))

instance (GenericCase a r, GenericCase b r, QA r) => GenericCase (a :+: b) r where
    type GCase (a :+: b) r = (GCase a r, GCase b r)
    type GRep (a :+: b) = (GRep' a, GRep' b)
    type GRep' (a :+: b) = GRep (a :+: b)
    galtCase (f, g) (Q e) = Q $ AppE2 Append (forget first) (forget second) (reify (undefined :: [r]))
       where
        (TupleT t1 t2) = typeExp e
        first :: Q [r]
        first = galtCase f (Q $ AppE1 Fst e t1 :: Q (a ()))
        second :: Q [r]
        second = galtCase g (Q $ AppE1 Snd e t2 :: Q (b ()))
    gcase fs e = Q $ AppE1 Head (forget alts) (reify (undefined :: r))
        where
          alts :: Q [r]
          alts = galtCase fs e

instance QA r => GenericCase U1 r where
    type GCase U1 r = Q () -> Q r
    type GRep U1 = ()
    gcase f (Q a) = f (Q a)

instance (GenericCase a r, GenericCase b r) => GenericCase (a :*: b) r where
    type GCase (a :*: b) r = Q (GRep a, GRep b) -> Q r
    type GRep (a :*: b) = (GRep a, GRep b)
    gcase f (Q a) = f (Q a)

instance GenericCase a r => GenericCase (M1 i c a) r where
    type GCase (M1 i c a) r = GCase a r
    type GRep (M1 i c a) = GRep a
    gcase f (Q a) = gcase f (Q a :: Q (a ()))

instance (QA a, QA r) => GenericCase (K1 i a) r where
    type GCase (K1 i a) r = Q a -> Q r
    type GRep  (K1 i a) = a
    gcase f (Q a) = f (Q a)

instance (QA r) => Case () r where

instance (QA a, QA b, QA r) => Case (a, b) r where

instance (QA a, QA b, QA c, QA r) => Case (a, b, c) r where

instance (QA a, QA b, QA r) => Case (Either a b) r where

instance (QA a, QA b) => QA (a, b) where

instance (QA a, QA b, QA c) => QA (a, b, c) where

instance (QA a, QA b, QA c, QA d) => QA (a, b, c, d) where

instance (QA a) => QA (Maybe a) where

instance (QA a,QA b) => QA (Either a b) where

tupleToEither :: (QA a,QA b) => Q ([a],[b]) -> Q (Either a b)
tupleToEither (Q x) = (Q x)

eitherToTuple :: (QA a,QA b) => Q (Either a b) -> Q ([a],[b])
eitherToTuple (Q x) = (Q x)


-- * Currying

class GCurry a where
  type GCurry1 a
  gCurry :: a -> GCurry1 a

-- class GUncurry a where
--   type GCurry2 a
--   gUncurry :: GCurry2 a -> a

class GUncurry a where
  type GCurry2 a
  gUncurry :: a -> a
  gUncurry = id

-- instance GCurry (Q r) where
--   type GCurry1 (Q r) = Q r
--   gCurry = id

instance GCurry ((a1 -> Q r) -> Q r) where
  type GCurry1 ((a1 -> Q r) -> Q r) = (a1 -> Q r) -> Q r
  gCurry = id

instance GCurry ((a1 -> Q r, a2 -> Q r) -> Q r) where
  type GCurry1 ((a1 -> Q r, a2 -> Q r) -> Q r) = (a1 -> Q r) -> (a2 -> Q r) -> Q r
  gCurry f = \a1 a2 -> f (a1,a2)

instance GCurry ((a1 -> Q r, (a2 -> Q r, a3 -> Q r)) -> Q r) where
  type GCurry1 ((a1 -> Q r, (a2 -> Q r, a3 -> Q r)) -> Q r) = (a1 -> Q r) -> (a2 -> Q r) -> (a3 -> Q r) -> Q r
  gCurry f = \a1 a2 a3 -> f (a1,(a2,a3))

instance (GUncurry (a1 -> Q r), GUncurry (a2 -> Q r), GUncurry (a3 -> Q r), GUncurry (a4 -> Q r)) => GCurry (((a1 -> Q r,a2 -> Q r),(a3 -> Q r, a4 -> Q r)) -> Q r) where
  type GCurry1 (((a1 -> Q r,a2 -> Q r),(a3 -> Q r, a4 -> Q r)) -> Q r) = (a1 -> Q r) -> (a2 -> Q r) -> (a3 -> Q r) -> (a4 -> Q r) -> Q r
  gCurry f = \a1 a2 a3 a4 -> f ((a1,a2),(a3,a4))

instance GUncurry a where
  type GCurry2 a = a
-- instance GUncurry (Q a1 -> Q r) where
--   type GCurry2 (Q a1 -> Q r) = Q a1 -> Q r
--   gUncurry = id
--
-- instance GUncurry ((Q a1,Q a2) -> Q r) where
--   type GCurry2 ((Q a1,Q a2) -> Q r) = Q a1 -> Q a2 -> Q r
--   gUncurry f = \(a1,a2) -> f a1 a2
--
-- instance GUncurry ((Q a1,(Q a2,Q a3)) -> Q r) where
--   type GCurry2 ((Q a1,(Q a2,Q a3)) -> Q r) = Q a1 -> Q a2 -> Q a3 -> Q r
--   gUncurry f = \(a1,(a2,a3)) -> f a1 a2 a3
--
-- instance GUncurry (((Q a1,Q a2),(Q a3,Q a4)) -> Q r) where
--   type GCurry2 (((Q a1,Q a2),(Q a3,Q a4)) -> Q r) = Q a1 -> Q a2 -> Q a3 -> Q a4 -> Q r
--   gUncurry f = \((a1,a2),(a3,a4)) -> f a1 a2 a3 a4

-- * Basic Types

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

-- * Eq, Ord and Num Instances for Databse Queries

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
             IntegerN i t   -> IntegerE i t
             DoubleN d t    -> DoubleE d t
             TupleN n1 n2 t -> TupleE (convert n1) (convert n2) t
             ListN ns t     -> ListE (map convert ns) t

forget :: Q a -> Exp
forget (Q a) = a

toLam1 :: forall a b. (QA a, QA b) => (Q a -> Q b) -> Exp
toLam1 f = LamE (forget . f . Q) (ArrowT (reify (undefined :: a)) (reify (undefined :: b)))

toLam2 :: forall a b c. (QA a, QA b, QA c) => (Q a -> Q b -> Q c) -> Exp
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
  fromString s = Q (TextE (T.pack s) TextT)