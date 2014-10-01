{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE ViewPatterns          #-}

module Database.DSH.Frontend.Externals where
       
import Database.DSH.Frontend.Internals
import Database.DSH.Frontend.TH
import Database.DSH.Frontend.Funs
import Database.DSH.Impossible

import Prelude ( Eq, Ord, Num(..), Fractional(..), Floating(..)
               , Bool(..), Char, Integer, Double, Maybe(..), Either(..)
               , id, ($), (.))
import qualified Prelude as P

import Data.String
import Data.Text (Text)
import qualified Data.Text as T

-- QA Instances

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

instance (QA a,QA b) => QA (a,b) where
  type Rep (a,b) = (Rep a,Rep b)
  toExp (a,b) = PairE (toExp a) (toExp b)
  frExp (PairE a b) = (frExp a,frExp b)
  frExp _ = $impossible

instance (QA a,QA b,QA c) => QA (a,b,c) where
  type Rep (a,b,c) = (Rep a, Rep b, Rep c)
  toExp (a,b,c) = TupleConstE (Tuple3E (toExp a) (toExp b) (toExp c))
  frExp (TupleConstE (Tuple3E a b c)) = (frExp a, frExp b, frExp c)
  frExp _ = $impossible

instance (QA a) => QA [a] where
  type Rep [a] = [Rep a]
  toExp as = ListE (P.map toExp as)
  frExp (ListE as) = P.map frExp as
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

-- Elim instances

instance (QA r) => Elim () r where
  type Eliminator () r = Q r -> Q r
  elim _ r = r

instance (QA r) => Elim Bool r where
  type Eliminator Bool r = Q r -> Q r -> Q r
  elim (Q e) (Q e1) (Q e2) = Q (AppE Cond (PairE e (PairE e1 e2)))

instance (QA r) => Elim Char r where
  type Eliminator Char r = (Q Char -> Q r) -> Q r
  elim q f = f q

instance (QA r) => Elim Integer r where
  type Eliminator Integer r = (Q Integer -> Q r) -> Q r
  elim q f = f q

instance (QA r) => Elim Double r where
  type Eliminator Double r = (Q Double -> Q r) -> Q r
  elim q f = f q

instance (QA r) => Elim Text r where
  type Eliminator Text r = (Q Text -> Q r) -> Q r
  elim q f = f q

instance (QA a,QA b,QA r) => Elim (a,b) r where
  type Eliminator (a,b) r = (Q a -> Q b -> Q r) -> Q r
  elim q f = f (fst q) (snd q)

instance (QA a,QA r) => Elim (Maybe a) r where
  type Eliminator (Maybe a) r = Q r -> (Q a -> Q r) -> Q r
  elim q r f = maybe r f q

instance (QA a,QA b,QA r) => Elim (Either a b) r where
  type Eliminator (Either a b) r = (Q a -> Q r) -> (Q b -> Q r) -> Q r
  elim q f g = either f g q

-- BasicType instances

instance BasicType () where
instance BasicType Bool where
instance BasicType Char where
instance BasicType Integer where
instance BasicType Double where
instance BasicType Text where

-- TA instances

instance TA () where
instance TA Bool where
instance TA Char where
instance TA Integer where
instance TA Double where
instance TA Text where
instance (BasicType a, BasicType b) => TA (a,b) where
instance (BasicType a, BasicType b, BasicType c) => TA (a,b,c) where

-- Num and Fractional instances

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

instance Floating (Exp Double) where
  pi     = DoubleE 3.141592653589793
  sin e  = AppE Sin e
  cos e  = AppE Cos e
  tan e  = AppE Tan e
  sqrt e = AppE Sqrt e
  exp e  = AppE Exp e
  log e  = AppE Log e
  asin e = AppE ASin e
  acos e = AppE ACos e
  atan e = AppE ATan e
  sinh   = $unimplemented
  cosh   = $unimplemented
  asinh  = $unimplemented
  atanh  = $unimplemented
  acosh  = $unimplemented

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

instance Floating (Q Double) where
  pi         = Q pi
  sin (Q e)  = Q (sin e)
  cos (Q e)  = Q (cos e)
  tan (Q e)  = Q (tan e)
  asin (Q e) = Q (asin e)
  acos (Q e) = Q (acos e)
  atan (Q e) = Q (atan e)
  exp (Q e)  = Q (exp e)
  log (Q e)  = Q (log e)
  sqrt (Q e) = Q (sqrt e)
  sinh   = $unimplemented
  cosh   = $unimplemented
  asinh  = $unimplemented
  atanh  = $unimplemented
  acosh  = $unimplemented

-- View instances

instance View (Q ()) where
  type ToView (Q ()) = Q ()
  view = id

instance View (Q Bool) where
  type ToView (Q Bool) = Q Bool
  view = id

instance View (Q Char) where
  type ToView (Q Char) = Q Char
  view = id

instance View (Q Integer) where
  type ToView (Q Integer) = Q Integer
  view = id

instance View (Q Double) where
  type ToView (Q Double) = Q Double
  view = id

instance View (Q Text) where
  type ToView (Q Text) = Q Text
  view = id

instance (QA a, QA b) => View (Q (a,b)) where
  type ToView (Q (a,b)) = (Q a,Q b)
  view (Q e) = (Q (AppE Fst e),Q (AppE Snd e))

instance (QA a,QA b,QA c) => View (Q (a,b,c)) where
    type ToView (Q (a,b,c)) = (Q a,Q b,Q c)
    view (Q e) = (Q (AppE (TupElem Tup3_1) e), Q (AppE (TupElem Tup3_2) e), Q (AppE (TupElem Tup3_3) e))

-- IsString instances

instance IsString (Q Text) where
  fromString = Q . TextE . T.pack

-- * Referring to persistent tables

defaultHints :: TableHints
defaultHints = TableHints [] PossiblyEmpty

table :: (QA a, TA a) => String -> TableHints -> Q [a]
table name hints = Q (TableE (TableDB name hints))

-- * toQ

toQ :: (QA a) => a -> Q a
toQ = Q . toExp

-- * Unit

unit :: Q ()
unit = Q UnitE

-- * Boolean logic

false :: Q Bool
false = Q (BoolE False)

true :: Q Bool
true = Q (BoolE True)

not :: Q Bool -> Q Bool
not (Q e) = Q (AppE Not e)

(&&) :: Q Bool -> Q Bool -> Q Bool
(&&) (Q a) (Q b) = Q (AppE Conj (PairE a b))

(||) :: Q Bool -> Q Bool -> Q Bool
(||) (Q a) (Q b) = Q (AppE Disj (PairE a b))

-- * Equality and Ordering

eq :: (QA a,Eq a,TA a) => Q a -> Q a -> Q Bool
eq (Q a) (Q b) = Q (AppE Equ (PairE a b))

(==) :: (QA a,Eq a,TA a) => Q a -> Q a -> Q Bool
(==) = eq

neq :: (QA a,Eq a,TA a) => Q a -> Q a -> Q Bool
neq (Q a) (Q b) = Q (AppE NEq (PairE a b))

(/=) :: (QA a,Eq a,TA a) => Q a -> Q a -> Q Bool
(/=) = neq

lt :: (QA a,Ord a,TA a) => Q a -> Q a -> Q Bool
lt (Q a) (Q b) = Q (AppE Lt (PairE a b))

(<) :: (QA a,Ord a,TA a) => Q a -> Q a -> Q Bool
(<) = lt

lte :: (QA a,Ord a,TA a) => Q a -> Q a -> Q Bool
lte (Q a) (Q b) = Q (AppE Lte (PairE a b))

(<=) :: (QA a,Ord a,TA a) => Q a -> Q a -> Q Bool
(<=) = lte

gte :: (QA a,Ord a,TA a) => Q a -> Q a -> Q Bool
gte (Q a) (Q b) = Q (AppE Gte (PairE a b))

(>=) :: (QA a,Ord a,TA a) => Q a -> Q a -> Q Bool
(>=) = gte

gt :: (QA a,Ord a,TA a) => Q a -> Q a -> Q Bool
gt (Q a) (Q b) = Q (AppE Gt (PairE a b))

(>) :: (QA a,Ord a,TA a) => Q a -> Q a -> Q Bool
(>) = gt

min :: (QA a,Ord a,TA a) => Q a -> Q a -> Q a
min a b = cond (a < b) a b

max :: (QA a,Ord a,TA a) => Q a -> Q a -> Q a
max a b = cond (a > b) a b
    
mod :: Q Integer -> Q Integer -> Q Integer
mod (Q a) (Q b) = Q (AppE Mod (PairE a b))

div :: Q Integer -> Q Integer -> Q Integer
div (Q a) (Q b) = Q (AppE Div (PairE a b))

-- * Conditionals

bool :: (QA a) => Q a -> Q a -> Q Bool -> Q a
bool f t b = cond b t f

cond :: (QA a) => Q Bool -> Q a -> Q a -> Q a
cond (Q c) (Q a) (Q b) = Q (AppE Cond (PairE c (PairE a b)))

ifThenElse :: (QA a) => Q Bool -> Q a -> Q a -> Q a
ifThenElse = cond

(?) :: (QA a) => Q Bool -> (Q a,Q a) -> Q a
(?) c (a,b) = cond c a b

-- * Maybe

listToMaybe :: (QA a) => Q [a] -> Q (Maybe a)
listToMaybe (Q as) = Q as

maybeToList :: (QA a) => Q (Maybe a) -> Q [a]
maybeToList (Q ma) = Q ma

nothing :: (QA a) => Q (Maybe a)
nothing = listToMaybe nil

just :: (QA a) => Q a -> Q (Maybe a)
just a = listToMaybe (singleton a)

isNothing :: (QA a) => Q (Maybe a) -> Q Bool
isNothing ma = null (maybeToList ma)

isJust :: (QA a) => Q (Maybe a) -> Q Bool
isJust ma = not (isNothing ma)

fromJust :: (QA a) => Q (Maybe a) -> Q a
fromJust ma = head (maybeToList ma)

maybe :: (QA a,QA b) => Q b -> (Q a -> Q b) -> Q (Maybe a) -> Q b
maybe b f ma = isNothing ma ? (b,f (fromJust ma))

fromMaybe :: (QA a) => Q a -> Q (Maybe a) -> Q a
fromMaybe a ma = isNothing ma ? (a,fromJust ma)

catMaybes :: (QA a) => Q [Maybe a] -> Q [a]
catMaybes = concatMap maybeToList

mapMaybe :: (QA a,QA b) => (Q a -> Q (Maybe b)) -> Q [a] -> Q [b]
mapMaybe f = concatMap (maybeToList . f)

-- * Either

pairToEither :: (QA a,QA b) => Q ([a],[b]) -> Q (Either a b)
pairToEither (Q a) = Q a

eitherToPair :: (QA a,QA b) => Q (Either a b) -> Q ([a],[b])
eitherToPair (Q a) = Q a

left :: (QA a,QA b) => Q a -> Q (Either a b)
left a = pairToEither (pair (singleton a) nil)

right :: (QA a,QA b) => Q b -> Q (Either a b)
right a = pairToEither (pair nil (singleton a))

isLeft :: (QA a,QA b) => Q (Either a b) -> Q Bool
isLeft = null . snd . eitherToPair

isRight :: (QA a,QA b) => Q (Either a b) -> Q Bool
isRight = null . fst . eitherToPair

either :: (QA a,QA b,QA c) => (Q a -> Q c) -> (Q b -> Q c) -> Q (Either a b) -> Q c
either lf rf e =
  let p = eitherToPair e
  in  head (map lf (fst p) ++ map rf (snd p))

lefts :: (QA a,QA b) => Q [Either a b] -> Q [a]
lefts = concatMap (fst . eitherToPair)

rights :: (QA a,QA b) => Q [Either a b] -> Q [b]
rights = concatMap (snd . eitherToPair)

partitionEithers :: (QA a,QA b) => Q [Either a b] -> Q ([a], [b])
partitionEithers es = pair (lefts es) (rights es)

-- * List Construction

nil :: (QA a) => Q [a]
nil = Q (ListE [])

empty :: (QA a) => Q [a]
empty = nil

cons :: (QA a) => Q a -> Q [a] -> Q [a]
cons (Q a) (Q as) = Q (AppE Cons (PairE a as))

(<|) :: (QA a) => Q a -> Q [a] -> Q [a]
(<|) = cons

snoc :: (QA a) => Q [a] -> Q a -> Q [a]
snoc as a = append as (singleton a)

(|>) :: (QA a) => Q [a] -> Q a -> Q [a]
(|>) = snoc

singleton :: (QA a) => Q a -> Q [a]
singleton (Q e) = cons (Q e) nil

-- * List Operations

head :: (QA a) => Q [a] -> Q a
head (Q as) = Q (AppE Head as)

tail :: (QA a) => Q [a] -> Q [a]
tail (Q as) = Q (AppE Tail as)

take :: (QA a) => Q Integer -> Q [a] -> Q [a]
take i xs = map fst $ filter (\xp -> snd xp <= i) $ number xs

drop :: (QA a) => Q Integer -> Q [a] -> Q [a]
drop i xs = map fst $ filter (\xp -> snd xp > i) $ number xs

map :: (QA a,QA b) => (Q a -> Q b) ->  Q [a] -> Q [b]
map f (Q as) = Q (AppE Map (PairE (LamE (toLam f)) as))

append :: (QA a) => Q [a] -> Q [a] -> Q [a]
append (Q as) (Q bs) = Q (AppE Append (PairE as bs))

(++) :: (QA a) => Q [a] -> Q [a] -> Q [a]
(++) = append

filter :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q [a]
filter f (Q as) = Q (AppE Filter (PairE (LamE (toLam f)) as))

-- | Partition a list into groups according to the supplied projection
-- function.
groupWithKey :: (QA a,QA b,Ord b, TA b) => (Q a -> Q b) -> Q [a] -> Q [(b,[a])]
groupWithKey f (Q as) = Q (AppE GroupWithKey (PairE (LamE (toLam f)) as))

groupWith :: (QA a,QA b,Ord b, TA b) => (Q a -> Q b) -> Q [a] -> Q [[a]]
groupWith f as = map snd (groupWithKey f as)

sortWith :: (QA a,QA b,Ord b, TA b) => (Q a -> Q b) -> Q [a] -> Q [a]
sortWith f (Q as) = Q (AppE SortWith (PairE (LamE (toLam f)) as))

last :: (QA a) => Q [a] -> Q a
last (Q as) = Q (AppE Last as)

init :: (QA a) => Q [a] -> Q [a]
init (Q as) = Q (AppE Init as)

null :: (QA a) => Q [a] -> Q Bool
null (Q as) = Q (AppE Null as)

length :: (QA a) => Q [a] -> Q Integer
length (Q as) = Q (AppE Length as)

index :: (QA a) => Q [a] -> Q Integer -> Q a
index (Q as) (Q i) = Q (AppE Index (PairE as i))

(!!) :: (QA a) => Q [a] -> Q Integer -> Q a
(!!) = index

reverse :: (QA a) => Q [a] -> Q [a]
reverse (Q as) = Q (AppE Reverse as)

number :: (QA a) => Q [a] -> Q [(a, Integer)]
number (Q as) = Q (AppE Number as)

-- * Special folds

and :: Q [Bool] -> Q Bool
and (Q bs) = Q (AppE And bs)

or :: Q [Bool] -> Q Bool
or (Q bs) = Q (AppE Or bs)

any :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q Bool
any f = or . map f

all :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q Bool
all f = and . map f

sum :: (QA a,Num a) => Q [a] -> Q a
sum (Q as) = Q (AppE Sum as)

avg :: (QA a,Num a) => Q [a] -> Q Double
avg (Q as) = Q (AppE Avg as)

concat :: (QA a) => Q [[a]] -> Q [a]
concat (Q ass) = Q (AppE Concat ass)

concatMap :: (QA a,QA b) => (Q a -> Q [b]) -> Q [a] -> Q [b]
concatMap f (Q as) = Q (AppE ConcatMap (PairE (LamE (toLam f)) as))

maximum :: (QA a,Ord a,TA a) => Q [a] -> Q a
maximum (Q as) = Q (AppE Maximum as)

minimum :: (QA a,Ord a,TA a) => Q [a] -> Q a
minimum (Q as) = Q (AppE Minimum as)

-- * Sublists

splitAt :: (QA a) => Q Integer -> Q [a] -> Q ([a],[a])
splitAt i xs = pair (take i xs) (drop i xs)

-- FIXME might be implemented using non-dense numbering!
takeWhile :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q [a]
takeWhile p xs = 
    let ys            = map (\xpos -> pair xpos (p $ fst xpos)) $ number xs
        notQualifying = filter (\xposp -> not (snd xposp)) ys
        maxPos = minimum $ map (\xposp -> snd $ fst xposp) notQualifying
     
    in cond (null notQualifying) 
            xs
            (map (\xposp -> fst $ fst xposp) $ filter (\xposp -> (snd $ fst xposp) < maxPos) ys)

-- FIXME might be implemented using non-dense numbering!
dropWhile :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q [a]
dropWhile p xs = 
    let ys  = map (\xpos -> pair xpos (p $ fst xpos)) $ number xs
        minPos = minimum $ map (\xposp -> snd $ fst xposp) $ filter (\xposp -> not (snd xposp)) ys
    in map (\xposp -> fst $ fst xposp) $ filter (\xposp -> (snd $ fst xposp) >= minPos) ys

span :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q ([a],[a])
span f as = pair (takeWhile f as) (dropWhile f as)

break :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q ([a],[a])
break f = span (not . f)

-- * Searching Lists

elem :: (QA a,Eq a,TA a) => Q a -> Q [a] -> Q Bool
elem a as = any (a ==) as

notElem :: (QA a,Eq a,TA a) => Q a -> Q [a] -> Q Bool
notElem a as = not (a `elem` as)

lookup :: (QA a,QA b,Eq a,TA a) => Q a -> Q [(a, b)] -> Q (Maybe b)
lookup a  = listToMaybe . map snd . filter ((a ==) . fst)

-- * Zipping and Unzipping Lists

zip :: (QA a,QA b) => Q [a] -> Q [b] -> Q [(a,b)]
zip (Q as) (Q bs) = Q (AppE Zip (PairE as bs))

zipWith :: (QA a,QA b,QA c) => (Q a -> Q b -> Q c) -> Q [a] -> Q [b] -> Q [c]
zipWith f as bs = map (\e -> f (fst e) (snd e)) (zip as bs)

unzip :: (QA a,QA b) => Q [(a,b)] -> Q ([a],[b])
unzip as = pair (map fst as) (map snd as)

zip3 :: (QA a,QA b,QA c) => Q [a] -> Q [b] -> Q [c] -> Q [(a,b,c)]
zip3 as bs cs = map (\abc -> triple (fst abc) (fst (snd abc)) (snd (snd abc))) (zip as (zip bs cs))

zipWith3 :: (QA a,QA b,QA c,QA d) => (Q a -> Q b -> Q c -> Q d) -> Q [a] -> Q [b] -> Q [c] -> Q [d]
zipWith3 f as bs cs = map (\e -> (case view e of (a,b,c) -> f a b c))
                          (zip3 as bs cs)

unzip3 :: (QA a,QA b,QA c) => Q [(a,b,c)] -> Q ([a],[b],[c])
unzip3 abcs = triple (map (\e -> (case view e of (a,_,_) -> a)) abcs)
                     (map (\e -> (case view e of (_,b,_) -> b)) abcs)
                     (map (\e -> (case view e of (_,_,c) -> c)) abcs)

-- * Set-oriented operations

nub :: (QA a,Eq a,TA a) => Q [a] -> Q [a]
nub (Q as) = Q (AppE Nub as)

-- * Tuple Projection Functions

fst :: (QA a,QA b) => Q (a,b) -> Q a
fst (Q e) = Q (AppE Fst e)

snd :: (QA a,QA b) => Q (a,b) -> Q b
snd (Q e) = Q (AppE Snd e)

-- * Conversions between numeric types

integerToDouble :: Q Integer -> Q Double
integerToDouble (Q i) = Q (AppE IntegerToDouble i)

-- * Text Functions

-- | 'like' matches a string (first argument) against a pattern (second
-- argument). The pattern must be a SQL LIKE pattern, that is use '_' for single
-- character wildcards and '_' for multi-character wildcards.
like :: Q Text -> Q Text -> Q Bool
like (Q t) (Q p) = Q (AppE Like (PairE t p))

-- * Matrix/Vector-like operators

-- | Transpose a matrix in nested-list representation
transpose :: QA a => Q [[a]] -> Q [[a]]
transpose (Q ass) = Q (AppE Transpose ass)

-- | Divide the list into sublists of length 'n'
-- FIXME should propably have a constraint to flat types
reshape :: QA a => Integer -> Q [a] -> Q [[a]]
reshape n (Q e) = Q (AppE (Reshape n) e)

-- * Rebind Monadic Combinators

return :: (QA a) => Q a -> Q [a]
return = singleton

(>>=) :: (QA a,QA b) => Q [a] -> (Q a -> Q [b]) -> Q [b]
(>>=) ma f = concatMap f ma

(>>) :: (QA a,QA b) => Q [a] -> Q [b] -> Q [b]
(>>) ma mb = concatMap (\_ -> mb) ma

mzip :: (QA a,QA b) => Q [a] -> Q [b] -> Q [(a,b)]
mzip = zip

guard :: Q Bool -> Q [()]
guard (Q c) = Q (AppE Guard c)

-- * Construction of tuples

pair :: (QA a,QA b) => Q a -> Q b -> Q (a,b)
pair (Q a) (Q b) = Q (PairE a b)

triple :: (QA a,QA b,QA c) => Q a -> Q b -> Q c -> Q (a,b,c)
triple (Q a) (Q b) (Q c)= Q (TupleConstE (Tuple3E a b c))

infixl 9  !!
infixr 5  ++, <|, |>
infix  4  ==, /=, <, <=, >=, >
infixr 3  &&
infixr 2  ||
infix  0  ?

deriveTupleRangeQA                4 16
deriveTupleRangeTA                4 16
deriveTupleRangeView              4 16
deriveTupleRangeSmartConstructors 4 16

-- * Missing functions

-- $missing
{- $missing

This module offers most of the functions on lists given in PreludeList for the
'Q' type. Missing functions are:

General folds:

> foldl
> foldl1
> scanl
> scanl1
> foldr
> foldr1
> scanr
> scanr1

Infinit lists:

> iterate
> repeat
> cycle

String functions:

> lines
> words
> unlines
> unwords

-}
