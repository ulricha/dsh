{-# LANGUAGE TemplateHaskell, ScopedTypeVariables, MultiParamTypeClasses, FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Database.DSH.Combinators where

import Database.DSH.Data
-- import Database.DSH.TH

import Prelude (Eq, Ord, Num, Bool(..), Integer, Double, Maybe, Either, undefined, ($), (.))

-- * Unit

unit :: Q ()
unit = expToQ UnitE 

-- * Boolean logic

false :: Q Bool
false = expToQ $ BoolE False

true :: Q Bool
true = expToQ $ BoolE True

not :: Q Bool -> Q Bool
not = expToQ . (App1E Not) . qToExp

(&&) :: Q Bool -> Q Bool -> Q Bool
(&&) = appE2 Conj

(||) :: Q Bool -> Q Bool -> Q Bool
(||) = appE2 Disj

-- * Equality and Ordering

eq :: (Eq a,QA a) => Q a -> Q a -> Q Bool
eq = appE2 Equ

(==) :: (Eq a,QA a) => Q a -> Q a -> Q Bool
(==) = eq

neq :: (Eq a,QA a) => Q a -> Q a -> Q Bool
neq a b = not (eq a b)

(/=) :: (Eq a,QA a) => Q a -> Q a -> Q Bool
(/=) = neq

lt :: (Ord a,QA a) => Q a -> Q a -> Q Bool
lt = appE2 Lt

(<) :: (Ord a,QA a) => Q a -> Q a -> Q Bool
(<) = lt

lte :: (Ord a,QA a) => Q a -> Q a -> Q Bool
lte = appE2 Lte 

(<=) :: (Ord a,QA a) => Q a -> Q a -> Q Bool
(<=) = lte

gte :: (Ord a,QA a) => Q a -> Q a -> Q Bool
gte = appE2 Gte

(>=) :: (Ord a,QA a) => Q a -> Q a -> Q Bool
(>=) = gte

gt :: (Ord a,QA a) => Q a -> Q a -> Q Bool
gt = appE2 Gt

(>) :: (Ord a,QA a) => Q a -> Q a -> Q Bool
(>) = gt

min :: forall a. (Ord a, QA a) => Q a -> Q a -> Q a
min = appE2 Min

max :: forall a. (Ord a, QA a) => Q a -> Q a -> Q a
max = appE2 Max

-- * Conditionals
-- | Boolean fold
-- | It's first argument is used in the case of False
-- | It's second argument is used in the case of True
-- | The third argument is the boolean
bool :: (QA a) => Q a -> Q a -> Q Bool -> Q a
bool f t b = cond b t f

cond :: forall a. (QA a) => Q Bool -> Q a -> Q a -> Q a
cond = appE3 Cond

(?) :: (QA a) => Q Bool -> (Q a,Q a) -> Q a
(?) c (a,b) = cond c a b
{-
-- * Maybe

listToMaybe :: QA a => Q [a] -> Q (Maybe a)
listToMaybe (Q as) = (Q as) 

maybeToList :: QA a => Q (Maybe a) -> Q [a]
maybeToList (Q ma) = (Q ma)

nothing :: QA a => Q (Maybe a)
nothing = listToMaybe nil

just :: QA a => Q a -> Q (Maybe a)
just a = listToMaybe (singleton a)

isNothing :: QA a => Q (Maybe a) -> Q Bool
isNothing ma = null (maybeToList ma)

isJust :: QA a => Q (Maybe a) -> Q Bool
isJust ma = not (isNothing ma)

fromJust :: QA a => Q (Maybe a) -> Q a
fromJust ma = head (maybeToList ma)

maybe :: (QA a, QA b) => Q b -> (Q a -> Q b) -> Q (Maybe a) -> Q b
maybe b f ma = (isNothing ma) ? (b, f (fromJust (ma)))

fromMaybe :: QA a => Q a -> Q (Maybe a) -> Q a
fromMaybe a ma = (isNothing ma) ? (a, fromJust (ma))

catMaybes :: QA a => Q [Maybe a] -> Q [a]
catMaybes mas = concatMap maybeToList mas

mapMaybe :: (QA a, QA b) => (Q a -> Q (Maybe b)) -> Q [a] -> Q [b]
mapMaybe f as = concatMap (maybeToList . f) as

-- * Either

left :: (QA a,QA b) => Q a -> Q (Either a b)
left a = tupleToEither (tuple ((singleton a),nil))

right :: (QA a,QA b) => Q b -> Q (Either a b)
right a = tupleToEither (tuple (nil,(singleton a)))

isLeft :: (QA a,QA b) => Q (Either a b) -> Q Bool
isLeft = null . snd . eitherToTuple

isRight :: (QA a,QA b) => Q (Either a b) -> Q Bool
isRight = null . fst . eitherToTuple

either :: (QA a,QA b,QA c) => (Q a -> Q c) -> (Q b -> Q c) -> Q (Either a b) -> Q c
either lf rf e = (isLeft e) ? ((lf . head . fst . eitherToTuple) e,(rf . head . snd . eitherToTuple) e)

lefts :: (QA a,QA b) => Q [Either a b] -> Q [a]
lefts = concatMap (fst . eitherToTuple)

rights :: (QA a,QA b) => Q [Either a b] -> Q [b]
rights = concatMap (snd . eitherToTuple)

partitionEithers :: (QA a,QA b) => Q [Either a b] -> Q ([a], [b])
partitionEithers es = tuple (lefts es,rights es)
-}
-- * List Construction

nil :: forall a. (QA a) => Q [a]
nil = expToQ $ ListE []

empty :: (QA a) => Q [a]
empty = nil

cons :: forall a. (QA a) => Q a -> Q [a] -> Q [a]
cons = appE2 Cons

(<|) :: (QA a) => Q a -> Q [a] -> Q [a]
(<|) = cons

snoc :: forall a. (QA a) => Q [a] -> Q a -> Q [a]
snoc = appE2 Snoc

(|>) :: (QA a) => Q [a] -> Q a -> Q [a]
(|>) = snoc

singleton :: (QA a) => Q a -> Q [a]
singleton a = cons a nil

-- * List Operations

head :: forall a. (QA a) => Q [a] -> Q a
head = appE1 Head

tail :: forall a. (QA a) => Q [a] -> Q [a]
tail = appE1 Tail

take :: forall a. (QA a) => Q Integer -> Q [a] -> Q [a]
take = appE2 Take

drop :: forall a. (QA a) => Q Integer -> Q [a] -> Q [a]
drop = appE2 Drop

map :: forall a b. (QA a, QA b) => (Q a -> Q b) ->  Q [a] -> Q [b]
map = appE2f Map 

append :: forall a. (QA a) => Q [a] -> Q [a] -> Q [a]
append = appE2 Append

(><) :: (QA a) => Q [a] -> Q [a] -> Q [a]
(><) = append

filter :: forall a. (QA a) => (Q a -> Q Bool) -> Q [a] -> Q [a]
filter = appE2f Filter

groupWith :: forall a b. (Ord b, QA a, QA b) => (Q a -> Q b) -> Q [a] -> Q [[a]]
groupWith = appE2f GroupWith

sortWith :: forall a b. (Ord b, QA a, QA b) => (Q a -> Q b) -> Q [a] -> Q [a]
sortWith = appE2f SortWith

the :: forall a. (Eq a, QA a) => Q [a] -> Q a
the = appE1 The

last :: forall a. (QA a) => Q [a] -> Q a
last = appE1 Last

init :: forall a. (QA a) => Q [a] -> Q [a]
init = appE1 Init

null :: (QA a) => Q [a] -> Q Bool
null = appE1 Null

length :: (QA a) => Q [a] -> Q Integer
length = appE1 Length

index :: forall a. (QA a) => Q [a] -> Q Integer -> Q a
index = appE2 Index

(!!) :: (QA a) => Q [a] -> Q Integer -> Q a
(!!) = index

reverse :: forall a. (QA a) => Q [a] -> Q [a]
reverse = appE1 Reverse


-- * Special folds

and :: Q [Bool] -> Q Bool
and = appE1 And

or :: Q [Bool] -> Q Bool
or = appE1 Or

any :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q Bool
any = appE2f Any 

all :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q Bool
all = appE2f All 

sum :: forall a. (QA a, Num a) => Q [a] -> Q a
sum = appE1 Sum

concat :: forall a. (QA a) => Q [[a]] -> Q [a]
concat = appE1 Concat

concatMap :: (QA a, QA b) => (Q a -> Q [b]) -> Q [a] -> Q [b]
concatMap f as = concat (map f as)

maximum   :: forall a. (QA a, Ord a) => Q [a] -> Q a
maximum = appE1 Maximum

minimum   :: forall a. (QA a, Ord a) => Q [a] -> Q a
minimum = appE1 Minimum

-- * Sublists

splitAt   :: forall a. (QA a) => Q Integer -> Q [a] -> Q ([a], [a])
splitAt = appE2 SplitAt

takeWhile :: forall a. (QA a) => (Q a -> Q Bool) -> Q [a] -> Q [a]
takeWhile = appE2f TakeWhile

dropWhile :: forall a. (QA a) => (Q a -> Q Bool) -> Q [a] -> Q [a]
dropWhile = appE2f DropWhile

span :: forall a. (QA a) => (Q a -> Q Bool) -> Q [a] -> Q ([a],[a])
span = appE2f Span

break :: forall a. (QA a) => (Q a -> Q Bool) -> Q [a] -> Q ([a],[a])
break = appE2f Break

-- * Searching Lists

elem :: forall a. (Eq a, QA a) => Q a -> Q [a] -> Q Bool
elem a as = (null (filter (a ==) as)) ? (false,true)

notElem :: forall a. (Eq a, QA a) => Q a -> Q [a] -> Q Bool
notElem a as = not (elem a as)

{-
lookup :: (QA a,QA b,Eq a) => Q a -> Q [(a, b)] -> Q (Maybe b)
lookup a  = listToMaybe . map snd . filter ((a ==) . fst)
-}
-- * Zipping and Unzipping Lists

zip :: forall a b. (QA a, QA b) => Q [a] -> Q [b] -> Q [(a,b)]
zip = appE2 Zip

zipWith   :: forall a b c. (QA a, QA b, QA c) => (Q a -> Q b -> Q c) -> Q [a] -> Q [b] -> Q [c]
zipWith = appE3f ZipWith

unzip :: forall a b. (QA a, QA b) => Q [(a,b)] -> Q ([a], [b])
unzip = appE1 Unzip

-- * "Set" operations

nub :: forall a. (Eq a,QA a) => Q [a] -> Q [a]
nub = appE1 Nub

-- * Tuple Projection Functions

fst :: forall a b. (QA a, QA b) => Q (a,b) -> Q a
fst = appE1 Fst

snd :: forall a b. (QA a, QA b) => Q (a,b) -> Q b
snd = appE1 Snd

pair :: forall a b. (QA a, QA b) => Q a -> Q b -> Q (a, b)
pair a b = expToQ (PairE (qToExp a) (qToExp b))

-- * Conversions between numeric types

integerToDouble :: Q Integer -> Q Double
integerToDouble = appE1 IntegerToDouble

-- * Rebind Monadic Combinators

return :: (QA a) => Q a -> Q [a]
return = singleton

(>>=) :: (QA a, QA b) => Q [a] -> (Q a -> Q [b]) -> Q [b]
(>>=) ma f = concatMap f ma

(>>) :: (QA a, QA b) => Q [a] -> Q [b] -> Q [b]
(>>) ma mb = concatMap (\_ -> mb) ma

mzip :: (QA a, QA b) => Q [a] -> Q [b] -> Q [(a,b)]
mzip = zip

guard :: Q Bool -> Q [()]
guard c = cond c (singleton unit) nil

infixl 9 !!
infixr 5 ><, <|, |>
infix  4  ==, /=, <, <=, >=, >
infixr 3  &&
infixr 2  ||
infix  0  ?

-- 'QA', 'TA' and 'View' instances for tuples up to the defined length.
{-
$(generateDeriveTupleQARange   5 7)
$(generateDeriveTupleTARange   3 7)
$(generateDeriveTupleViewRange 3 7)
-}
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

Zipping and unzipping lists:

> zip3
> zipWith3
> unzip3

-}
