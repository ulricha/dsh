{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

import Data.String
import Data.Text (Text)
import qualified Data.Text as T

data Exp a where
  UnitE     :: Exp ()
  BoolE     :: Bool     -> Exp Bool
  CharE     :: Char     -> Exp Char
  IntegerE  :: Integer  -> Exp Integer
  DoubleE   :: Double   -> Exp Double
  TextE     :: Text     -> Exp Text

  PairE     :: (QA a,QA b)  => Exp a -> Exp b -> Exp (a,b)
  NilE      :: (QA a)       => Exp [a]
  ConsE     :: (QA a)       => Exp a -> Exp [a] -> Exp [a]
  AppE      :: (QA a,QA b)  => Fun (Exp a) (Exp b) -> Exp a -> Exp b
  LamE      :: (QA a,QA b)  => (Exp a -> Exp b) -> Exp (a -> b)
  VarE      :: (QA a)       => Integer -> Exp a
  TableE    :: (QA a)       => Table -> Exp [a]

data Fun a b where
  Fst     :: (QA a,QA b)  => Fun (Exp (a,b)) (Exp a)
  Snd     :: (QA a,QA b)  => Fun (Exp (a,b)) (Exp b)
  Add     :: (QA a)       => Fun (Exp (a,a)) (Exp a)
  Mul     :: (QA a)       => Fun (Exp (a,a)) (Exp a)
  Sub     :: (QA a)       => Fun (Exp (a,a)) (Exp a)
  Div     :: (QA a)       => Fun (Exp (a,a)) (Exp a)
  Lt      :: (QA a)       => Fun (Exp (a,a)) (Exp Bool)
  Lte     :: (QA a)       => Fun (Exp (a,a)) (Exp Bool)
  Equ     :: (QA a)       => Fun (Exp (a,a)) (Exp Bool)
  Gte     :: (QA a)       => Fun (Exp (a,a)) (Exp Bool)
  Gt      :: (QA a)       => Fun (Exp (a,a)) (Exp Bool)
  Cond    :: (QA a)       => Fun (Exp (Bool,(a,a))) (Exp a)
  Map     :: (QA a,QA b)  => Fun (Exp (a -> b),Exp [a]) (Exp b)
  Concat  :: (QA a)       => Fun (Exp [[a]]) (Exp [a])
             
data Norm a where
  UnitN     :: Norm ()
  BoolN     :: Bool     -> Norm Bool
  CharN     :: Char     -> Norm Char
  IntegerN  :: Integer  -> Norm Integer
  DoubleN   :: Double   -> Norm Double
  TextN     :: Text     -> Norm Text

  PairN     :: (QA a,QA b)  => Norm a -> Norm b -> Norm (a,b)
  NilN      :: (QA a)       => Norm [a]
  ConsN     :: (QA a)       => Norm a -> Norm [a] -> Norm [a]

normToExp :: Norm a -> Exp a
normToExp (UnitN) = UnitE
normToExp (BoolN b) = BoolE b
normToExp (CharN c) = CharE c
normToExp (IntegerN i) = IntegerE i
normToExp (DoubleN d) = DoubleE d
normToExp (TextN t) = TextE t
normToExp (PairN a b) = PairE (normToExp a) (normToExp b)
normToExp (NilN) = NilE
normToExp (ConsN a as) = ConsE (normToExp a) (normToExp as)

data Type =
    UnitT
  | BoolT
  | CharT
  | IntegerT
  | DoubleT
  | TextT
  | PairT Type Type
  | ListT Type
  | ArrowT Type Type
  deriving (Eq, Ord, Show)

data Table =
    TableDB   String [[String]]
  | TableCSV  String
  deriving (Eq, Ord, Show)

class QA a where
  data Q a
  type E a
  reify   :: a -> Type
  toQ     :: a -> Q a
  toNorm  :: a -> Norm (E a)
  frNorm  :: Norm (E a) -> a
  qToExp  :: Q a -> Exp (E a)
  expToQ  :: Exp (E a) -> Q a

instance QA () where
  data Q () = UnitQ (Exp ())
  type E () = ()
  reify _ = UnitT
  toQ = UnitQ . normToExp . toNorm
  toNorm () = UnitN
  frNorm UnitN = ()
  qToExp (UnitQ e) = e
  expToQ = UnitQ

instance QA Bool where
  data Q Bool = BoolQ (Exp Bool)
  type E Bool = Bool
  reify _ = BoolT
  toQ = BoolQ . normToExp . toNorm
  toNorm b = BoolN b
  frNorm (BoolN b) = b
  qToExp (BoolQ e) = e
  expToQ = BoolQ

instance QA Char where
  data Q Char = CharQ (Exp Char)
  type E Char = Char
  reify _ = CharT
  toQ = CharQ . normToExp . toNorm
  toNorm b = CharN b
  frNorm (CharN b) = b
  qToExp (CharQ e) = e
  expToQ = CharQ

instance QA Integer where
  data Q Integer = IntegerQ (Exp Integer)
  type E Integer = Integer
  reify _ = IntegerT
  toQ = IntegerQ . normToExp . toNorm
  toNorm b = IntegerN b
  frNorm (IntegerN b) = b
  qToExp (IntegerQ e) = e
  expToQ = IntegerQ

instance QA Double where
  data Q Double = DoubleQ (Exp Double)
  type E Double = Double
  reify _ = DoubleT
  toQ = DoubleQ . normToExp . toNorm
  toNorm b = DoubleN b
  frNorm (DoubleN b) = b
  qToExp (DoubleQ e) = e
  expToQ = DoubleQ

instance QA Text where
  data Q Text = TextQ (Exp Text)
  type E Text = Text
  reify _ = TextT
  toQ = TextQ . normToExp . toNorm
  toNorm t = TextN t
  frNorm (TextN t) = t
  qToExp (TextQ e) = e
  expToQ = TextQ

instance (QA a,QA (E a),QA b,QA (E b)) => QA (a,b) where
  data Q (a,b) = PairQ (Exp (E a,E b))
  type E (a,b) = (E a,E b)
  reify _ = PairT (reify (undefined :: a)) (reify (undefined :: b))
  toQ = PairQ . normToExp . toNorm
  toNorm (a,b) = PairN (toNorm a) (toNorm b)
  frNorm (PairN a b) = (frNorm a,frNorm b)
  qToExp (PairQ e) = e
  expToQ = PairQ

instance (QA a, QA (E a)) => QA [a] where
  data Q [a] = ListQ (Exp [E a])
  type E [a] = [E a]
  reify _ = ListT (reify (undefined :: a))
  toQ = ListQ . normToExp . toNorm
  toNorm [] = NilN
  toNorm (a : as) = ConsN (toNorm a) (toNorm as)
  frNorm NilN = []
  frNorm (ConsN a as) = frNorm a : frNorm as
  qToExp (ListQ e) = e 
  expToQ = ListQ

instance (QA a, QA (E a)) => QA (Maybe a) where
  data Q (Maybe a) = MaybeQ (Exp [E a])
  type E (Maybe a) = [E a]
  reify _ = ListT (reify (undefined :: a))
  toQ = MaybeQ . normToExp . toNorm
  toNorm Nothing = NilN
  toNorm (Just a) = ConsN (toNorm a) NilN
  frNorm (NilN) = Nothing
  frNorm (ConsN a _) = Just (frNorm a)
  qToExp (MaybeQ e) = e
  expToQ = MaybeQ

-- * Basic Types

class BasicType a where

instance BasicType () where
instance BasicType Bool where
instance BasicType Char where
instance BasicType Integer where
instance BasicType Double where
instance BasicType Text where

-- * Refering to Real Database Tables

class TA a where

instance TA () where
instance TA Bool where
instance TA Char where
instance TA Integer where
instance TA Double where
instance TA Text where
instance (BasicType a, BasicType b) => TA (a,b) where

table :: (QA a, QA (E a), TA a) => String -> Q [a]
table name = ListQ (TableE (TableDB name []))

tableDB :: (QA a, QA (E a), TA a) => String -> Q [a]
tableDB name = ListQ (TableE (TableDB name []))

tableWithKeys :: (QA a, QA (E a), TA a) => String -> [[String]] -> Q [a]
tableWithKeys name keys = ListQ (TableE (TableDB name keys))

tableCSV :: (QA a, QA (E a), TA a) => String -> Q [a]
tableCSV filename = ListQ (TableE (TableCSV filename))

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

instance Num (Q Integer) where
  (+) q1 q2 = expToQ (qToExp q1 + qToExp q2)
  (*) q1 q2 = expToQ (qToExp q1 * qToExp q2)
  (-) q1 q2 = expToQ (qToExp q1 - qToExp q2)
  fromInteger = expToQ . fromInteger
  abs = expToQ . abs . qToExp
  signum = expToQ . signum . qToExp

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

instance Num (Q Double) where
  (+) q1 q2 = expToQ (qToExp q1 + qToExp q2)
  (*) q1 q2 = expToQ (qToExp q1 * qToExp q2)
  (-) q1 q2 = expToQ (qToExp q1 - qToExp q2)
  fromInteger = expToQ . fromInteger
  abs = expToQ . abs . qToExp
  signum = expToQ . signum . qToExp

instance Fractional (Exp Double) where
  (/) e1 e2    = AppE Div (PairE e1 e2)
  fromRational = DoubleE . fromRational

instance Fractional (Q Double) where
  (/) q1 q2    = expToQ (qToExp q1 / qToExp q2)
  fromRational = expToQ . fromRational

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

instance (QA a,QA (E a),QA b,QA (E b),QA (E (E a)), QA (E (E b))) => View (Q (a,b)) (Q a,Q b) where
  type ToView (Q (a,b)) = (Q a,Q b)
  type FromView (Q a,Q b) = Q (a,b)
  view (PairQ e) = (expToQ (AppE Fst e), expToQ (AppE Snd e))
  fromView (a,b) = expToQ (PairE (qToExp a) (qToExp b))

-- -- instance Convertible Norm Exp where
-- --     safeConvert n = Right $
-- --         case n of
-- --              UnitN t        -> UnitE t
-- --              BoolN b t      -> BoolE b t
-- --              CharN c t      -> CharE c t
-- --              TextN s t      -> TextE s t
-- --              IntegerN i t   -> IntegerE i t
-- --              DoubleN d t    -> DoubleE d t
-- --              TupleN n1 n2 t -> TupleE (convert n1) (convert n2) t
-- --              ListN ns t     -> ListE (map convert ns) t
-- -- 
-- -- forget :: Q a -> Exp
-- -- forget (Q a) = a
-- -- 
-- -- toLam1 :: forall a b. (QA a, QA b) => (Q a -> Q b) -> Exp
-- -- toLam1 f = LamE (forget . f . Q) (ArrowT (reify (undefined :: a)) (reify (undefined :: b)))
-- -- 
-- -- toLam2 :: forall a b c. (QA a, QA b, QA c) => (Q a -> Q b -> Q c) -> Exp
-- -- toLam2 f =
-- --   let f1 = \a b -> forget (f (Q a) (Q b))
-- --       t1 = ArrowT (reify (undefined :: b)) (reify (undefined :: c))
-- --       f2 = \a -> LamE (\b -> f1 a b) t1
-- --       t2 = ArrowT (reify (undefined :: a)) t1
-- --   in  LamE f2 t2
-- -- 
-- -- unfoldType :: Type -> [Type]
-- -- unfoldType (TupleT t1 t2) = t1 : unfoldType t2
-- -- unfoldType t = [t]
-- -- 
-- -- instance Convertible Type SqlTypeId where
-- --     safeConvert n =
-- --         case n of
-- --              IntegerT       -> Right SqlBigIntT
-- --              DoubleT        -> Right SqlDoubleT
-- --              BoolT          -> Right SqlBitT
-- --              CharT          -> Right SqlCharT
-- --              TextT          -> Right SqlVarCharT
-- --              UnitT          -> convError "No `UnitT' representation" n
-- --              TupleT {}      -> convError "No `TupleT' representation" n
-- --              ListT {}       -> convError "No `ListT' representation" n
-- --              ArrowT {}      -> convError "No `ArrowT' representation" n
-- -- 
-- -- instance Convertible SqlTypeId Type where
-- --     safeConvert n =
-- --         case n of
-- --           SqlCharT           -> Right TextT
-- --           SqlVarCharT        -> Right TextT
-- --           SqlLongVarCharT    -> Right TextT
-- --           SqlWCharT          -> Right TextT
-- --           SqlWVarCharT       -> Right TextT
-- --           SqlWLongVarCharT   -> Right TextT
-- --           SqlDecimalT        -> Right DoubleT
-- --           SqlNumericT        -> Right DoubleT
-- --           SqlSmallIntT       -> Right IntegerT
-- --           SqlIntegerT        -> Right IntegerT
-- --           SqlRealT           -> Right DoubleT
-- --           SqlFloatT          -> Right DoubleT
-- --           SqlDoubleT         -> Right DoubleT
-- --           SqlBitT            -> Right BoolT
-- --           SqlBigIntT         -> Right IntegerT
-- --           SqlTinyIntT        -> Right IntegerT
-- --           _                  -> convError "Unsupported `SqlTypeId'" n
-- -- 
-- -- 
-- -- instance Convertible SqlValue Norm where
-- --     safeConvert sql =
-- --         case sql of
-- --              SqlNull            -> Right $ UnitN UnitT
-- --              SqlInteger i       -> Right $ IntegerN i IntegerT
-- --              SqlDouble d        -> Right $ DoubleN d DoubleT
-- --              SqlBool b          -> Right $ BoolN b BoolT
-- --              SqlChar c          -> Right $ CharN c CharT
-- --              SqlString t        -> Right $ TextN (T.pack t) TextT
-- --              SqlByteString s    -> Right $ TextN (T.decodeUtf8 s) TextT
-- --              _                  -> convError "Unsupported `SqlValue'" sql
-- -- 
-- -- instance Convertible (SqlValue, Type) Norm where
-- --     safeConvert sql =
-- --         case sql of
-- --           (SqlNull, UnitT)         -> Right $ UnitN UnitT
-- -- 
-- --           (SqlInteger i, IntegerT) -> Right $ IntegerN i IntegerT
-- --           (SqlInt32 i, IntegerT)   -> Right $ flip IntegerN IntegerT $ convert i
-- --           (SqlInt64 i, IntegerT)   -> Right $ flip IntegerN IntegerT $ convert i
-- --           (SqlWord32 i, IntegerT)  -> Right $ flip IntegerN IntegerT $ convert i
-- --           (SqlWord64 i, IntegerT)  -> Right $ flip IntegerN IntegerT $ convert i
-- --           (SqlRational r, IntegerT) -> Right $ flip IntegerN IntegerT $ convert r
-- -- 
-- --           (SqlDouble d, DoubleT)   -> Right $ DoubleN d DoubleT
-- --           (SqlRational r, DoubleT) -> Right $ flip DoubleN DoubleT $ convert r
-- --           (SqlInteger i, DoubleT)  -> Right $ flip DoubleN DoubleT $ convert i
-- --           (SqlInt32 i, DoubleT)    -> Right $ flip DoubleN DoubleT $ convert i
-- --           (SqlInt64 i, DoubleT)    -> Right $ flip DoubleN DoubleT $ convert i
-- --           (SqlWord32 i, DoubleT)   -> Right $ flip DoubleN DoubleT $ convert i
-- --           (SqlWord64 i, DoubleT)   -> Right $ flip DoubleN DoubleT $ convert i
-- -- 
-- --           (SqlBool b, BoolT)       -> Right $ BoolN b BoolT
-- --           (SqlInteger i, BoolT)    -> Right $ BoolN (i == 1) BoolT
-- --           (SqlInt32 i, BoolT)      -> Right $ BoolN (i == 1) BoolT
-- --           (SqlInt64 i, BoolT)      -> Right $ BoolN (i == 1) BoolT
-- --           (SqlWord32 i, BoolT)     -> Right $ BoolN (i == 1) BoolT
-- --           (SqlWord64 i, BoolT)     -> Right $ BoolN (i == 1) BoolT
-- -- 
-- --           (SqlString s, TextT)     -> Right $ TextN (T.pack s) TextT
-- --           (SqlByteString s, TextT) -> Right $ TextN (T.decodeUtf8 s) TextT
-- -- 
-- --           (SqlChar c, CharT) -> Right $ CharN c CharT
-- --           (SqlString (c : _), CharT) -> Right $ CharN c CharT
-- --           (SqlByteString ((T.unpack . T.decodeUtf8) -> (c : _)), CharT)  -> Right $ CharN c CharT
-- -- 
-- --           _                        -> $impossible
-- -- 
-- -- instance Convertible Norm SqlValue where
-- --     safeConvert n =
-- --         case n of
-- --              UnitN _             -> Right $ SqlNull
-- --              IntegerN i _        -> Right $ SqlInteger i
-- --              DoubleN d _         -> Right $ SqlDouble d
-- --              BoolN b _           -> Right $ SqlBool b
-- --              CharN c _           -> Right $ SqlChar c
-- --              TextN t _           -> Right $ SqlString $ T.unpack t
-- --              ListN _ _           -> convError "Cannot convert `Norm' to `SqlValue'" n
-- --              TupleN _ _ _        -> convError "Cannot convert `Norm' to `SqlValue'" n


instance IsString (Q Text) where
  fromString s = TextQ (TextE (T.pack s))