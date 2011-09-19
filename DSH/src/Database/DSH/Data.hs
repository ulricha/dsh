{-# LANGUAGE TemplateHaskell, ScopedTypeVariables, ViewPatterns, EmptyDataDecls, MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances, FlexibleContexts, UndecidableInstances, DeriveDataTypeable #-}

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

data S
data L

data Q ta a = Q Exp deriving (Show, Data, Typeable)

class QA a b | a -> b, b -> a where
  reify    :: a -> Type
  toNorm   :: a -> Norm
  fromNorm :: Norm -> a
  toQ      :: a -> b

instance QA () (Q S ()) where
  reify _ = UnitT
  toNorm _ = UnitN UnitT
  fromNorm (UnitN UnitT) = ()
  fromNorm _ = $impossible
  toQ = Q . convert . toNorm

instance QA Bool (Q S Bool) where
  reify _ = BoolT
  toNorm b = BoolN b BoolT
  fromNorm (BoolN b BoolT) = b
  fromNorm v = $impossible
  toQ = Q . convert . toNorm

instance QA Char (Q S Char) where
  reify _ = CharT
  toNorm c = CharN c CharT
  fromNorm (CharN c CharT) = c
  fromNorm _ = $impossible
  toQ = Q . convert . toNorm

instance QA Integer (Q S Integer) where
  reify _ = IntegerT
  toNorm i = IntegerN i IntegerT
  fromNorm (IntegerN i IntegerT) = i
  fromNorm _ = $impossible
  toQ = Q . convert . toNorm

instance QA Double (Q S Double) where
  reify _ = DoubleT
  toNorm d = DoubleN d DoubleT
  fromNorm (DoubleN i DoubleT) = i
  fromNorm _ = $impossible
  toQ = Q . convert . toNorm

instance QA Text (Q S Text) where
  reify _ = TextT
  toNorm t = TextN t TextT
  fromNorm (TextN t TextT) = t
  fromNorm _ = $impossible
  toQ = Q . convert . toNorm

instance (QA a a1, QA b b1) => QA (a,b) (Q S (a1,b1)) where
  reify _ = TupleT (reify (undefined :: a)) (reify (undefined :: b))
  toNorm (a,b) = TupleN (toNorm a) (toNorm b) (reify (a,b))
  fromNorm (TupleN a b (TupleT _ _)) = (fromNorm a,fromNorm b)
  fromNorm _ = $impossible
  toQ = Q . convert . toNorm

instance (QA a a1, QA b b1, QA c c1) => QA (a,b,c) (Q S (a1,b1,c1)) where
  reify _ = TupleT (reify (undefined :: a)) (TupleT (reify (undefined :: b)) (reify (undefined :: c)))
  toNorm (a,b,c) = TupleN (toNorm a) (TupleN (toNorm b) (toNorm c) (reify (b,c))) (reify (a,b,c))
  fromNorm (TupleN a (TupleN b c (TupleT _ _)) (TupleT _ _)) = (fromNorm a,fromNorm b,fromNorm c)
  fromNorm _ = $impossible
  toQ = Q . convert . toNorm

instance (QA a b) => QA [a] (Q L b) where
  reify _ = ListT (reify (undefined :: a))
  toNorm as = ListN (map toNorm as) (reify as)
  fromNorm (ListN as (ListT _)) = map fromNorm as
  fromNorm _ = $impossible
  toQ = Q . convert . toNorm

instance (QA a b) => QA (Maybe a) (Q S (Maybe b)) where
  reify _ = reify ([] :: [a])

  toNorm Nothing  = toNorm ([] :: [a])
  toNorm (Just x) = toNorm [x]

  fromNorm ma = case (fromNorm ma) :: [a] of
                  []      -> Nothing
                  (x : _) -> Just x

  toQ = Q . convert . toNorm

instance (QA a c,QA b d) => QA (Either a b) (Q S (Either c d)) where
  reify _ = reify (([],[]) :: ([a],[b]))

  toNorm (Left  x) = toNorm ([x],[] :: [b])
  toNorm (Right x) = toNorm ([] :: [a],[x])

  fromNorm e =  case (fromNorm e) :: ([a],[b]) of
                  ([],x : _) -> Right x
                  (x : _,[]) -> Left  x
                  _          -> $impossible
  toQ = Q . convert . toNorm-- 

tupleToEither ::  (QA a (Q tc c),QA b (Q td d)) =>
                  Q S (Q L (Q tc c),Q L (Q td d)) -> Q S (Either (Q tc c) (Q td d))
tupleToEither (Q x) = (Q x)

eitherToTuple ::  (QA a (Q tc c),QA b (Q td d)) =>
                  Q S (Either (Q tc c) (Q td d)) -> Q S (Q L (Q tc c),Q L (Q td d))
eitherToTuple (Q x) = (Q x)

-- * Refering to Real Database Tables

class (QA a b) => TA a b where
  tablePersistence :: Table -> b

table :: (TA a b) => String -> b
table = tableDB

tableDB :: (TA a b) => String -> b
tableDB name = tablePersistence (TableDB name [])

tableWithKeys :: (TA a b) => String -> [[String]] -> b
tableWithKeys name keys = tablePersistence (TableDB name keys)

tableCSV :: (TA a b) => String -> b
tableCSV filename = tablePersistence (TableCSV filename)

instance TA [()] (Q L (Q S ())) where
  tablePersistence t = Q (TableE t (reify (undefined :: [()])))

instance TA [Bool] (Q L (Q S Bool)) where
  tablePersistence t = Q (TableE t (reify (undefined :: [Bool])))

instance TA [Char] (Q L (Q S Char)) where
  tablePersistence t = Q (TableE t (reify (undefined :: [Char])))

instance TA [Integer] (Q L (Q S Integer)) where
  tablePersistence t = Q (TableE t (reify (undefined :: [Integer])))

instance TA [Double] (Q L (Q S Double)) where
  tablePersistence t = Q (TableE t (reify (undefined :: [Double])))

instance TA [Text] (Q L (Q S Text)) where
  tablePersistence t = Q (TableE t (reify (undefined :: [Text])))

instance (TA a a1,TA b b1) => TA (a,b) (Q S (a1,b1)) where
  tablePersistence t = Q (TableE t (reify (undefined :: [(a,b)])))

instance (TA a a1,TA b b1,TA c c1) => TA (a,b,c) (Q S (a1,b1,c1)) where
  tablePersistence t = Q (TableE t (reify (undefined :: [(a,b,c)])))

-- * Eq, Ord and Num Instances for Databse Queries

instance Eq (Q S Integer) where
  (==) _ _ = error "Eq instance for (Q Integer) must not be used."

instance Eq (Q S Double) where
  (==) _ _ = error "Eq instance for (Q Double) must not be used."

instance Num (Q S Integer) where
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

instance Num (Q S Double) where
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


instance Fractional (Q S Double) where
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

instance View (Q S ()) (Q S ()) where
  view = id
  fromView = id

instance View (Q S Bool) (Q S Bool) where
  view = id
  fromView = id

instance View (Q S Char) (Q S Char) where
  view = id
  fromView = id

instance View (Q S Integer) (Q S Integer) where
  view = id
  fromView = id

instance View (Q S Double) (Q S Double) where
  view = id
  fromView = id

instance View (Q S Text) (Q S Text) where
  view = id
  fromView = id

instance (QA a1 (Q ta a),QA b1 (Q tb b)) => View (Q S (Q ta a,Q tb b)) (Q ta a, Q tb b) where
  view (Q a) = (Q (AppE1 Fst a (reify (undefined :: a1))), Q (AppE1 Snd a (reify (undefined :: b1))))
  fromView ((Q e1),(Q e2)) = Q (TupleE e1 e2 (reify (undefined :: (a1, b1))))

instance (QA a1 (Q ta a),QA b1 (Q tb b), QA c1 (Q tc c)) => View (Q S (Q ta a,Q tb b, Q tc c)) (Q ta a, Q tb b, Q tc c) where
  view (Q a) =  ( Q (AppE1 Fst a (reify (undefined :: a1)))
                , Q (AppE1 Fst (AppE1 Snd a (reify (undefined :: (b1,c1)))) (reify (undefined :: b1)))
                , Q (AppE1 Snd (AppE1 Snd a (reify (undefined :: (b1,c1)))) (reify (undefined :: c1)))
                )
  fromView ((Q e1),(Q e2),(Q e3)) = Q (TupleE e1 (TupleE e2 e3 (reify (undefined :: (b1, c1)))) (reify (undefined :: (a1,(b1,c1)))))


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

forget :: Q ta a -> Exp
forget (Q a) = a

-- toLam1 :: forall a b a1 b1 ta tb. (QA a1 (Q ta a),QA b1 (Q tb b)) => (Q ta a -> Q tb b) -> Exp
-- toLam1 f = LamE (forget . f . Q) (ArrowT (reify (undefined :: a1)) (reify (undefined :: b1)))

toLam1 :: (Q ta a -> Q tb b) -> Exp
toLam1 f = LamE (forget . f . Q) undefined -- (ArrowT (reify (undefined :: a1)) (reify (undefined :: b1)))

toLam2 :: forall a b c a1 b1 c1 ta tb tc. (QA a1 (Q ta a),QA b1 (Q tb b), QA c1 (Q tc c)) => (Q ta a -> Q tb b -> Q tc c) -> Exp
toLam2 f =
  let f1 = \a b -> forget (f (Q a) (Q b))
      t1 = ArrowT (reify (undefined :: b1)) (reify (undefined :: c1))
      f2 = \a -> LamE (\b -> f1 a b) t1
      t2 = ArrowT (reify (undefined :: a1)) t1
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


instance IsString (Q S Text) where
  fromString s = Q (TextE (T.pack s) TextT)