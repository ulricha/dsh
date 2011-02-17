{-# LANGUAGE TemplateHaskell, ScopedTypeVariables, MultiParamTypeClasses, FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Database.DSH.Combinators where

import Database.DSH.Data
import Database.DSH.TH

import Data.Convertible

import Prelude (Eq, Ord, Num, Bool(..), Integer, Double, undefined, error, ($))

-- * Unit

unit :: Q ()
unit = Q (UnitE $ reify (undefined :: ()))

-- * Boolean logic

false :: Q Bool
false = Q (BoolE False BoolT)

true :: Q Bool
true = Q (BoolE True BoolT)

not :: Q Bool -> Q Bool
not (Q b) = Q (AppE1 Not b $ reify (undefined :: Bool))

(&&) :: Q Bool -> Q Bool -> Q Bool
(&&) (Q a) (Q b) = Q (AppE2 Conj a b $ reify (undefined :: Bool))

(||) :: Q Bool -> Q Bool -> Q Bool
(||) (Q a) (Q b) = Q (AppE2 Disj a b $ reify (undefined :: Bool))

-- * Equality and Ordering

eq :: (Eq a,QA a) => Q a -> Q a -> Q Bool
eq (Q a) (Q b) = Q (AppE2 Equ a b $ reify (undefined :: Bool))

(==) :: (Eq a,QA a) => Q a -> Q a -> Q Bool
(==) = eq

neq :: (Eq a,QA a) => Q a -> Q a -> Q Bool
neq a b = not (eq a b)

(/=) :: (Eq a,QA a) => Q a -> Q a -> Q Bool
(/=) = neq

lt :: (Ord a,QA a) => Q a -> Q a -> Q Bool
lt (Q a) (Q b) = Q (AppE2 Lt a b $ reify (undefined :: Bool))

(<) :: (Ord a,QA a) => Q a -> Q a -> Q Bool
(<) = lt

lte :: (Ord a,QA a) => Q a -> Q a -> Q Bool
lte (Q a) (Q b) = Q (AppE2 Lte a b $ reify (undefined :: Bool))

(<=) :: (Ord a,QA a) => Q a -> Q a -> Q Bool
(<=) = lte

gte :: (Ord a,QA a) => Q a -> Q a -> Q Bool
gte (Q a) (Q b) = Q (AppE2 Gte a b $ reify (undefined :: Bool))

(>=) :: (Ord a,QA a) => Q a -> Q a -> Q Bool
(>=) = gte

gt :: (Ord a,QA a) => Q a -> Q a -> Q Bool
gt (Q a) (Q b) = Q (AppE2 Gt a b $ reify (undefined :: Bool))

(>) :: (Ord a,QA a) => Q a -> Q a -> Q Bool
(>) = gt

min :: forall a. (Ord a, QA a) => Q a -> Q a -> Q a
min (Q a) (Q b) = Q (AppE2 Min a b $ reify (undefined :: a))

max :: forall a. (Ord a, QA a) => Q a -> Q a -> Q a
max (Q a) (Q b) = Q (AppE2 Max a b $ reify (undefined :: a))


-- * Conditionals

cond :: (QA a) => Q a -> Q a -> Q Bool -> Q a
cond a b c = c ? (a,b)

bool :: (QA a) => Q a -> Q a -> Q Bool -> Q a
bool = cond

(?) :: forall a. (QA a) => Q Bool -> (Q a,Q a) -> Q a
(?) (Q c) (Q a,Q b) = Q (AppE3 Cond c a b $ reify (undefined :: a))

-- * List Construction

nil :: forall a. (QA a) => Q [a]
nil = Q (ListE [] $ reify (undefined :: [a]))

empty :: (QA a) => Q [a]
empty = nil

cons :: forall a. (QA a) => Q a -> Q [a] -> Q [a]
cons (Q a) (Q as) = Q (AppE2 Cons a as $ reify (undefined :: [a]))

(<|) :: (QA a) => Q a -> Q [a] -> Q [a]
(<|) = cons

snoc :: forall a. (QA a) => Q [a] -> Q a -> Q [a]
snoc (Q as) (Q a) = Q (AppE2 Snoc as a $ reify (undefined :: [a]))

(|>) :: (QA a) => Q [a] -> Q a -> Q [a]
(|>) = snoc

singleton :: (QA a) => Q a -> Q [a]
singleton a = cons a nil

-- * List Operations

head :: forall a. (QA a) => Q [a] -> Q a
head (Q as) = Q (AppE1 Head as $ reify (undefined :: a))

tail :: forall a. (QA a) => Q [a] -> Q [a]
tail (Q as) = Q (AppE1 Tail as $ reify (undefined :: [a]))

take :: forall a. (QA a) => Q Integer -> Q [a] -> Q [a]
take (Q i) (Q as) = Q (AppE2 Take i as $ reify (undefined :: [a]))

drop :: forall a. (QA a) => Q Integer -> Q [a] -> Q [a]
drop (Q i) (Q as) = Q (AppE2 Drop i as $ reify (undefined :: [a]))

map :: forall a b. (QA a, QA b) => (Q a -> Q b) ->  Q [a] -> Q [b]
map f (Q as) = Q (AppE2 Map (toLam1 f) as $ reify (undefined :: [b]))

append :: forall a. (QA a) => Q [a] -> Q [a] -> Q [a]
append (Q as) (Q bs) = Q (AppE2 Append as bs $ reify (undefined :: [a]))

(><) :: (QA a) => Q [a] -> Q [a] -> Q [a]
(><) = append

filter :: forall a. (QA a) => (Q a -> Q Bool) -> Q [a] -> Q [a]
filter f (Q as) = Q (AppE2 Filter (toLam1 f) as $ reify (undefined :: [a]))

groupWith :: forall a b. (Ord b, QA a, QA b) => (Q a -> Q b) -> Q [a] -> Q [[a]]
groupWith f (Q as) = Q (AppE2 GroupWith (toLam1 f) as $ reify (undefined :: [[a]]))

sortWith :: forall a b. (Ord b, QA a, QA b) => (Q a -> Q b) -> Q [a] -> Q [a]
sortWith f (Q as) = Q (AppE2 SortWith (toLam1 f) as $ reify (undefined :: [a]))

the :: forall a. (Eq a, QA a) => Q [a] -> Q a
the (Q as) = Q (AppE1 The as $ reify (undefined :: a))

last :: forall a. (QA a) => Q [a] -> Q a
last (Q as) = Q (AppE1 Last as $ reify (undefined :: a))

init :: forall a. (QA a) => Q [a] -> Q [a]
init (Q as) = Q (AppE1 Init as $ reify (undefined :: [a]))

null :: (QA a) => Q [a] -> Q Bool
null (Q as) = Q (AppE1 Null as $ reify (undefined :: Bool))

length :: (QA a) => Q [a] -> Q Integer
length (Q as) = Q (AppE1 Length as $ reify (undefined :: Integer))

index :: forall a. (QA a) => Q [a] -> Q Integer -> Q a
index (Q as) (Q i) = Q (AppE2 Index as i $ reify (undefined :: a))

(!!) :: (QA a) => Q [a] -> Q Integer -> Q a
(!!) = index

reverse :: forall a. (QA a) => Q [a] -> Q [a]
reverse (Q as) = Q (AppE1 Reverse as $ reify (undefined :: [a]))


-- * Special folds

and       :: Q [Bool] -> Q Bool
and (Q as) = Q (AppE1 And as $ reify (undefined :: Bool))

or        :: Q [Bool] -> Q Bool
or (Q as) = Q (AppE1 Or as $ reify (undefined :: Bool))

any       :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q Bool
any f (Q as) = Q (AppE2 Any (toLam1 f) as $ reify (undefined :: Bool))

all       :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q Bool
all f (Q as) = Q (AppE2 All (toLam1 f) as $ reify (undefined :: Bool))

sum       :: forall a. (QA a, Num a) => Q [a] -> Q a
sum (Q as) = Q (AppE1 Sum as $ reify (undefined :: a))

concat    :: forall a. (QA a) => Q [[a]] -> Q [a]
concat (Q as) = Q (AppE1 Concat as $ reify (undefined :: [a]))

concatMap :: (QA a, QA b) => (Q a -> Q [b]) -> Q [a] -> Q [b]
concatMap f as = concat (map f as)

maximum   :: forall a. (QA a, Ord a) => Q [a] -> Q a
maximum (Q as) = Q (AppE1 Maximum as $ reify (undefined :: a))

minimum   :: forall a. (QA a, Ord a) => Q [a] -> Q a
minimum (Q as) = Q (AppE1 Minimum as $ reify (undefined :: a))

-- * Sublists

splitAt   :: forall a. (QA a) => Q Integer -> Q [a] -> Q ([a], [a])
splitAt (Q i) (Q as) = Q (AppE2 SplitAt i as $ reify (undefined :: ([a],[a])))

takeWhile :: forall a. (QA a) => (Q a -> Q Bool) -> Q [a] -> Q [a]
takeWhile f (Q as) = Q (AppE2 TakeWhile (toLam1 f) as $ reify (undefined :: [a]))

dropWhile :: forall a. (QA a) => (Q a -> Q Bool) -> Q [a] -> Q [a]
dropWhile f (Q as) = Q (AppE2 DropWhile (toLam1 f) as $ reify (undefined :: [a]))

span      :: forall a. (QA a) => (Q a -> Q Bool) -> Q [a] -> Q ([a],[a])
span f (Q as) = Q (AppE2 Span (toLam1 f) as $ reify (undefined :: ([a],[a])))

break     :: forall a. (QA a) => (Q a -> Q Bool) -> Q [a] -> Q ([a],[a])
break f (Q as) = Q (AppE2 Break (toLam1 f) as $ reify (undefined :: ([a],[a])))


-- * Searching Lists

elem :: forall a. (Eq a, QA a) => Q a -> Q [a] -> Q Bool
elem a as = (null (filter (a ==) as)) ? (false,true)

notElem :: forall a. (Eq a, QA a) => Q a -> Q [a] -> Q Bool
notElem a as = not (elem a as)

-- * Zipping and Unzipping Lists

zip       :: forall a b. (QA a, QA b) => Q [a] -> Q [b] -> Q [(a,b)]
zip (Q as) (Q bs) = Q (AppE2 Zip as bs $ reify (undefined :: [(a,b)]))

zipWith   :: forall a b c. (QA a, QA b, QA c) => (Q a -> Q b -> Q c) -> Q [a] -> Q [b] -> Q [c]
zipWith f (Q as) (Q bs) = Q (AppE3 ZipWith (toLam2 f) as bs $ reify (undefined :: [c]))

unzip     :: forall a b. (QA a, QA b) => Q [(a,b)] -> Q ([a], [b])
unzip (Q as) = Q (AppE1 Unzip as  $ reify (undefined :: ([a],[b])))

-- * "Set" operations

nub :: forall a. (Eq a,QA a) => Q [a] -> Q [a]
nub (Q as) = Q (AppE1 Nub as $ reify (undefined :: [a])) 


-- * Tuple Projection Functions

fst :: forall a b. (QA a, QA b) => Q (a,b) -> Q a
fst (Q a) = Q (AppE1 Fst a $ reify (undefined :: a))

snd :: forall a b. (QA a, QA b) => Q (a,b) -> Q b
snd (Q a) = Q (AppE1 Snd a $ reify (undefined :: b))


-- * Conversions between numeric types

integerToDouble :: Q Integer -> Q Double
integerToDouble (Q a) = Q (AppE1 IntegerToDouble a DoubleT)

-- * Convert Haskell values into DB queries

toQ   :: forall a. (QA a) => a -> Q a
toQ c = Q (convert (toNorm c))


infixl 9 !!
infixr 5 ><, <|, |>
infix  4  ==, /=, <, <=, >=, >
infixr 3  &&
infixr 2  ||
infix  0  ?

-- 'QA', 'TA' and 'View' instances for tuples up to the defined length.

$(generateDeriveTupleQARange   3 8)
$(generateDeriveTupleTARange   3 8)
$(generateDeriveTupleViewRange 3 8)


-- * Missing Combinators
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

Searching lists:

> lookup

Zipping and unzipping lists:

> zip3
> zipWith3
> unzip3

-}
