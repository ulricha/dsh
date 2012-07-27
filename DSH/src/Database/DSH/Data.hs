{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TemplateHaskell #-}
module Database.DSH.Data where


import Data.String
import Data.Text (Text)
import qualified Data.Text as T
import Database.DSH.Impossible

data Exp a where
  UnitE     :: Exp ()
  BoolE     :: Bool     -> Exp Bool
  CharE     :: Char     -> Exp Char
  IntegerE  :: Integer  -> Exp Integer
  DoubleE   :: Double   -> Exp Double
  TextE     :: Text     -> Exp Text

  PairE     :: (QA a,QA b)  => Exp a -> Exp b -> Exp (a,b)
  ListE     :: (QA a)       => [Exp a] -> Exp [a]
{-  NilE      :: (QA a)       => Exp [a]
  ConsE     :: (QA a)       => Exp a -> Exp [a] -> Exp [a] -}
  AppE1     :: QA b => Fun1 (Exp a) (Exp b) -> Exp a -> Exp b
  AppE2     :: Fun2 (Exp a) (Exp b) (Exp c) -> Exp a -> Exp b -> Exp c
  AppE3     :: Fun3 (Exp a) (Exp b) (Exp c) (Exp d) -> Exp a -> Exp b -> Exp c -> Exp d 
  LamE      :: (Exp a -> Exp b) -> Exp (a -> b)
  VarE      :: (QA a)       => Integer -> Exp a
  TableE    :: (QA a)       => Table -> Exp [a]

--The system with just one app and one type of function primitive doesn't work. 
-- When currying for map we need to construct a tuple that contains a function 
-- which itself is not in the QA class. Using a normal tuple prevents us from 
-- exploiting the types.

-- What is the value of NilE and ConsE as primitives, for optimisation it is easier if we just have lists and have cons as a function.
    
-- PairE should also be a function, might actually move it there once I have functions that work.

data Fun1 a b where
    Fst             ::          Fun1 (Exp (a,b))    (Exp a)
    Snd             ::          Fun1 (Exp (a,b))    (Exp b)
    Not             ::          Fun1 (Exp Bool)     (Exp Bool)
    Concat          ::          Fun1 (Exp [[a]])    (Exp [a])
    Head            ::          Fun1 (Exp [a])      (Exp a)
    Tail            ::          Fun1 (Exp [a])      (Exp [a])
    The             ::          Fun1 (Exp [a])      (Exp a)
    Init            ::          Fun1 (Exp [a])      (Exp [a])
    Last            ::          Fun1 (Exp [a])      (Exp a)
    Null            ::          Fun1 (Exp [a])      (Exp Bool)
    Length          ::          Fun1 (Exp [a])      (Exp Integer)
    Reverse         ::          Fun1 (Exp [a])      (Exp [a])
    And             ::          Fun1 (Exp [Bool])   (Exp Bool)
    Or              ::          Fun1 (Exp [Bool])   (Exp Bool)
    Sum             :: Num a => Fun1 (Exp [a])      (Exp a)
    Maximum         :: Ord a => Fun1 (Exp [a])      (Exp a)
    Minimum         :: Ord a => Fun1 (Exp [a])      (Exp a)
    Unzip           ::          Fun1 (Exp [(a, b)]) (Exp ([a], [b]))
    Nub             ::          Fun1 (Exp [a])      (Exp [a])
    IntegerToDouble ::          Fun1 (Exp Integer)  (Exp Double)
    
instance Show (Fun1 a b) where
    show Fst = "Fst"
    show Snd = "Snd"
    show Not = "Not"
    show Concat = "Concat"
    show Head = "Head"
    show Tail = "Tail"
    show The = "The"
    show Init = "Init"
    show Last = "Last"
    show Null = "Null"
    show Length = "Length"
    show Reverse = "Reverse"
    show And = "And"
    show Or = "Or"
    show Sum = "Sum"
    show Maximum = "Maximum"
    show Minimum = "Minimum"
    show Unzip = "Unzip"
    show Nub = "Nub"
    show IntegerToDouble = "IntegerToDouble"
    
appE1 :: (QA a, QA b) => (Fun1 (Exp a) (Exp b)) -> Q a -> Q b
appE1 f e1 = expToQ $ AppE1 f (qToExp e1)

data Fun2 a b c where
    Add       :: Num a => Fun2 (Exp a)            (Exp a)       (Exp a)
    Mul       :: Num a => Fun2 (Exp a)            (Exp a)       (Exp a)
    Sub       :: Num a => Fun2 (Exp a)            (Exp a)       (Exp a)
    Div       :: Num a => Fun2 (Exp a)            (Exp a)       (Exp a)
    Lt        :: Ord a => Fun2 (Exp a)            (Exp a)       (Exp Bool)
    Lte       :: Ord a => Fun2 (Exp a)            (Exp a)       (Exp Bool)
    Equ       :: Eq a  => Fun2 (Exp a)            (Exp a)       (Exp Bool)
    Gte       :: Ord a => Fun2 (Exp a)            (Exp a)       (Exp Bool)
    Gt        :: Ord a => Fun2 (Exp a)            (Exp a)       (Exp Bool)
    Conj      ::          Fun2 (Exp Bool)         (Exp Bool)    (Exp Bool)
    Disj      ::          Fun2 (Exp Bool)         (Exp Bool)    (Exp Bool)
    Min       :: Ord a => Fun2 (Exp a)            (Exp a)       (Exp a)
    Max       :: Ord a => Fun2 (Exp a)            (Exp a)       (Exp a)
    Map       ::          Fun2 (Exp (a -> b))     (Exp [a])     (Exp [b])
    Cons      ::          Fun2 (Exp a)            (Exp [a])     (Exp [a])
    Snoc      ::          Fun2 (Exp [a])          (Exp a)       (Exp [a])
    Take      ::          Fun2 (Exp Integer)      (Exp [a])     (Exp [a])
    Drop      ::          Fun2 (Exp Integer)      (Exp [a])     (Exp [a])
    Append    ::          Fun2 (Exp [a])          (Exp [a])     (Exp [a])
    Filter    ::          Fun2 (Exp (a -> Bool))  (Exp [a])     (Exp [a])
    GroupWith ::          Fun2 (Exp (a -> b))     (Exp [a])     (Exp [[a]])
    SortWith  :: Ord b => Fun2 (Exp (a -> b))     (Exp [a])     (Exp [a])
    Index     ::          Fun2 (Exp [a])          (Exp Integer) (Exp a)
    Any       ::          Fun2 (Exp (a -> Bool))  (Exp [a])     (Exp Bool)
    All       ::          Fun2 (Exp (a -> Bool))  (Exp [a])     (Exp Bool)
    SplitAt   ::          Fun2 (Exp Integer)      (Exp [a])     (Exp ([a], [a]))
    TakeWhile ::          Fun2 (Exp (a -> Bool))  (Exp [a])     (Exp [a])
    DropWhile ::          Fun2 (Exp (a -> Bool))  (Exp [a])     (Exp [a])
    Span      ::          Fun2 (Exp (a -> Bool))  (Exp [a])     (Exp ([a], [a]))
    Break     ::          Fun2 (Exp (a -> Bool))  (Exp [a])     (Exp ([a], [a]))
    Zip       ::          Fun2 (Exp [a])          (Exp [b])     (Exp [(a, b)])


appE2 :: (QA a, QA b, QA c) => (Fun2 (Exp a) (Exp b) (Exp c)) -> Q a -> Q b -> Q c
appE2 f e1 e2 = expToQ $ AppE2 f (qToExp e1) (qToExp e2)

appE2f :: (QA a, QA b, QA c, QA d) => (Fun2 (Exp (a -> b)) (Exp c) (Exp d)) -> (Q a -> Q b) -> Q c -> Q d
appE2f f l e1 = expToQ $ AppE2 f (toLam1 l) (qToExp e1) 
    
data Fun3 a b c d where
    Cond    :: Fun3 (Exp Bool)          (Exp a) (Exp a) (Exp a)
    ZipWith :: Fun3 (Exp (a -> b -> c)) (Exp [a]) (Exp [b]) (Exp [c])

appE3 :: (QA a, QA b, QA c, QA d) => (Fun3 (Exp a) (Exp b) (Exp c) (Exp d)) -> Q a -> Q b -> Q c -> Q d
appE3 f e1 e2 e3 = expToQ $ AppE3 f (qToExp e1) (qToExp e2) (qToExp e3)

appE3f :: (QA a, QA b, QA c, QA d, QA e, QA f) => Fun3 (Exp (a -> b -> c)) (Exp d) (Exp e) (Exp f) -> (Q a -> Q b -> Q c) -> Q d -> Q e -> Q f
appE3f f l e1 e2 = expToQ $ AppE3 f (toLam2 l) (qToExp e1) (qToExp e2)
    
data Norm a where
--  Rep       :: (QA a)   => Norm (E a) -> Norm a
  UnitN     :: Norm ()
  BoolN     :: Bool     -> Norm Bool
  CharN     :: Char     -> Norm Char
  IntegerN  :: Integer  -> Norm Integer
  DoubleN   :: Double   -> Norm Double
  TextN     :: Text     -> Norm Text

  PairN     :: (QA a,QA b)  => Norm a -> Norm b -> Norm (a,b)
  ListN     :: (QA a)       => [Norm a] -> Norm [a]
{-  NilN      :: (QA a)       => Norm [a]
  ConsN     :: (QA a)       => Norm a -> Norm [a] -> Norm [a] -}

normToExp :: Norm a -> Exp a
normToExp (UnitN) = UnitE
normToExp (BoolN b) = BoolE b
normToExp (CharN c) = CharE c
normToExp (IntegerN i) = IntegerE i
normToExp (DoubleN d) = DoubleE d
normToExp (TextN t) = TextE t
normToExp (PairN a b) = PairE (normToExp a) (normToExp b)

{-
normToExp (NilN) = NilE
normToExp (ConsN a as) = ConsE (normToExp a) (normToExp as)
-}
data Type a where
    UnitT :: Type ()
    BoolT :: Type Bool
    CharT :: Type Char
    IntegerT :: Type Integer
    DoubleT :: Type Double
    TextT :: Type Text
    PairT :: (DSHInternals a, DSHInternals b) => Type a -> Type b -> Type (a, b) 
    ListT :: DSHInternals a => Type a -> Type [a]
    ArrowT :: (DSHInternals a, DSHInternals b) => Type a -> Type b -> Type (a -> b)
  -- deriving (Eq, Ord, Show)

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

data Table =
    TableDB   String [[String]]
  | TableCSV  String
  deriving (Eq, Ord, Show)

class (DSHInternals a) => QA a where
  data Q a
--  reify   :: a -> Type a
  toQ     :: a -> Q a
  toNorm  :: a -> Norm a
  fromNorm  :: Norm a -> a
  qToExp  :: Q a -> Exp a
  expToQ  :: Exp a -> Q a

-- Not being able to reify function types works somewhat crippling we need another class that contains reify so that we can define an instance for it.

class DSHInternals a where
    reify :: a -> Type a
    
instance DSHInternals () where
    reify _ = UnitT

instance QA () where
  data Q () = UnitQ (Exp ())
  -- reify _ = UnitT
  toQ = UnitQ . normToExp . toNorm
  toNorm () = UnitN
  fromNorm UnitN = ()
  qToExp (UnitQ e) = e
  expToQ = UnitQ

instance DSHInternals Bool where
    reify _ = BoolT

instance QA Bool where
  data Q Bool = BoolQ (Exp Bool)
  -- reify _ = BoolT
  toQ = BoolQ . normToExp . toNorm
  toNorm b = BoolN b
  fromNorm (BoolN b) = b
  qToExp (BoolQ e) = e
  expToQ = BoolQ

instance DSHInternals Char where
    reify _ = CharT

instance QA Char where
  data Q Char = CharQ (Exp Char)
  -- reify _ = CharT
  toQ = CharQ . normToExp . toNorm
  toNorm b = CharN b
  fromNorm (CharN b) = b
  qToExp (CharQ e) = e
  expToQ = CharQ

instance DSHInternals Integer where
    reify _ = IntegerT

instance QA Integer where
  data Q Integer = IntegerQ (Exp Integer)
  -- reify _ = IntegerT
  toQ = IntegerQ . normToExp . toNorm
  toNorm b = IntegerN b
  fromNorm (IntegerN b) = b
  qToExp (IntegerQ e) = e
  expToQ = IntegerQ

instance DSHInternals Double where
    reify _ = DoubleT

instance QA Double where
  data Q Double = DoubleQ (Exp Double)
  -- reify _ = DoubleT
  toQ = DoubleQ . normToExp . toNorm
  toNorm b = DoubleN b
  fromNorm (DoubleN b) = b
  qToExp (DoubleQ e) = e
  expToQ = DoubleQ

instance DSHInternals Text where
    reify _ = TextT

instance QA Text where
  data Q Text = TextQ (Exp Text)
  -- reify _ = TextT
  toQ = TextQ . normToExp . toNorm
  toNorm t = TextN t
  fromNorm (TextN t) = t
  qToExp (TextQ e) = e
  expToQ = TextQ

instance (DSHInternals a, DSHInternals b) => DSHInternals (a, b) where
    reify _ = PairT (reify undefined) (reify undefined)

instance (QA a, QA b) => QA (a,b) where
  data Q (a,b) = PairQ (Exp (a, b))
  -- reify _ = PairT (reify (undefined :: a)) (reify (undefined :: b))
  toQ = PairQ . normToExp . toNorm
  toNorm (a,b) = PairN (toNorm a) (toNorm b)
  fromNorm (PairN a b) = (fromNorm a,fromNorm b)
  qToExp (PairQ e) = e
  expToQ = PairQ

instance (DSHInternals a) => DSHInternals [a] where
    reify _ = ListT (reify undefined)

instance (QA a) => QA [a] where
  data Q [a] = ListQ (Exp [a])
  -- reify _ = ListT (reify (undefined :: a))
  toQ = ListQ . normToExp . toNorm
  toNorm xs = ListN (map toNorm xs)
{-  toNorm [] = NilN
  toNorm (a : as) = ConsN (toNorm a) (toNorm as) -}
  fromNorm (ListN xs) = map fromNorm xs
{-  fromNorm NilN = []
  fromNorm (ConsN a as) = fromNorm a : fromNorm as -}
  qToExp (ListQ e) = e 
  expToQ = ListQ

instance (DSHInternals a, DSHInternals b) => DSHInternals (a -> b) where
    reify _ = ArrowT (reify undefined) (reify undefined)

{-
instance (QA a, QA (E a)) => QA (Maybe a) where
  data Q (Maybe a) = MaybeQ (Exp [E a])
  type E (Maybe a) = [E a]
  reify _ = ListT (reify (undefined :: a))
  toQ = MaybeQ . normToExp . toNorm
  {- toNorm Nothing = NilN
  toNorm (Just a) = ConsN (toNorm a) NilN -}
  toNorm Nothing = ListN []
  toNorm (Just a) = ListN [toNorm a]
  {- fromNorm (NilN) = Nothing
  fromNorm (ConsN a _) = Just (fromNorm a) -}
  fromNorm (ListN []) = Nothing
  fromNorm (ListN [a]) = Just (fromNorm a)
  qToExp (MaybeQ e) = e
  expToQ = MaybeQ
-}
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

table :: (QA a, TA a) => String -> Q [a]
table name = ListQ (TableE (TableDB name []))

tableDB :: (QA a, TA a) => String -> Q [a]
tableDB name = ListQ (TableE (TableDB name []))

tableWithKeys :: (QA a, TA a) => String -> [[String]] -> Q [a]
tableWithKeys name keys = ListQ (TableE (TableDB name keys))

tableCSV :: (QA a, TA a) => String -> Q [a]
tableCSV filename = ListQ (TableE (TableCSV filename))

-- * Eq, Ord and Num Instances for Databse Queries

instance Num (Exp Integer) where
  (+) e1 e2 = AppE2 Add e1 e2
  (*) e1 e2 = AppE2 Mul e1 e2
  (-) e1 e2 = AppE2 Sub e1 e2

  fromInteger = IntegerE

  abs e = let c = AppE2 Lt e 0
          in  AppE3 Cond c (negate e) e
      
  signum e = let c1 = AppE2 Lt  e 0
                 c2 = AppE2 Equ e 0
                 e' = AppE3 Cond c2 0 1
             in  AppE3 Cond c1 (-1) e'

instance Num (Q Integer) where
  (+) q1 q2 = expToQ (qToExp q1 + qToExp q2)
  (*) q1 q2 = expToQ (qToExp q1 * qToExp q2)
  (-) q1 q2 = expToQ (qToExp q1 - qToExp q2)
  fromInteger = expToQ . fromInteger
  abs = expToQ . abs . qToExp
  signum = expToQ . signum . qToExp

instance Num (Exp Double) where
  (+) e1 e2 = AppE2 Add e1 e2
  (*) e1 e2 = AppE2 Mul e1 e2
  (-) e1 e2 = AppE2 Sub e1 e2

  fromInteger = DoubleE . fromInteger

  abs e = let c = AppE2 Lt e 0
          in  AppE3 Cond c (negate e) e
      
  signum e = let c1 = AppE2 Lt  e 0
                 c2 = AppE2 Equ e 0
                 e' = AppE3 Cond c2 0 1
             in  AppE3 Cond c1 (-1) e'

instance Num (Q Double) where
  (+) q1 q2 = expToQ (qToExp q1 + qToExp q2)
  (*) q1 q2 = expToQ (qToExp q1 * qToExp q2)
  (-) q1 q2 = expToQ (qToExp q1 - qToExp q2)
  fromInteger = expToQ . fromInteger
  abs = expToQ . abs . qToExp
  signum = expToQ . signum . qToExp

instance Fractional (Exp Double) where
  (/) e1 e2    = AppE2 Div e1 e2
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

instance (QA a,QA b) => View (Q (a,b)) (Q a,Q b) where
  type ToView (Q (a,b)) = (Q a,Q b)
  type FromView (Q a,Q b) = Q (a,b)
  view (PairQ e) = (expToQ (AppE1 Fst e), expToQ (AppE1 Snd e))
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
-- -- 

toLam1 :: forall a b. (QA a, QA b) => (Q a -> Q b) -> Exp (a -> b)
toLam1 f = LamE (qToExp . f . expToQ)


toLam2 :: forall a b c. (QA a, QA b, QA c) => (Q a -> Q b -> Q c) -> Exp (a -> b -> c)
toLam2 f =
  let f1 = \a b -> qToExp (f a b)
      f2 = \a -> LamE (\b -> f1 (expToQ a) (expToQ b))
  in  LamE f2
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