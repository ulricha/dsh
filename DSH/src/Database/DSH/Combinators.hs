{-# LANGUAGE TemplateHaskell, ScopedTypeVariables, MultiParamTypeClasses, FlexibleInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Database.DSH.Combinators where

import Database.DSH.Data
-- import Database.DSH.TH

import Data.Convertible

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
not = expToQ . (AppE Not) . qToExp

(&&) :: Q Bool -> Q Bool -> Q Bool
(&&) a b = expToQ $ AppE And $ qToExp $ pair a b


(||) :: Q Bool -> Q Bool -> Q Bool
(||) a b = expToQ $ AppE Or $ qToExp $ pair a b

-- * Equality and Ordering

eq :: (Eq a,QA a) => Q a -> Q a -> Q Bool
eq a b = expToQ $ AppE Equ $ qToExp $ pair a b

(==) :: (Eq a,QA a) => Q a -> Q a -> Q Bool
(==) = eq

neq :: (Eq a,QA a) => Q a -> Q a -> Q Bool
neq a b = not (eq a b)

(/=) :: (Eq a,QA a) => Q a -> Q a -> Q Bool
(/=) = neq

lt :: (Ord a,QA a) => Q a -> Q a -> Q Bool
lt a b = expToQ $ AppE Lt $ qToExp $ pair a b

(<) :: (Ord a,QA a) => Q a -> Q a -> Q Bool
(<) = lt

lte :: (Ord a,QA a) => Q a -> Q a -> Q Bool
lte a b = expToQ $ AppE Lte $ qToExp $ pair a b

(<=) :: (Ord a,QA a) => Q a -> Q a -> Q Bool
(<=) = lte

gte :: (Ord a,QA a) => Q a -> Q a -> Q Bool
gte a b = expToQ $ AppE Gte $ qToExp $ pair a b

(>=) :: (Ord a,QA a) => Q a -> Q a -> Q Bool
(>=) = gte

gt :: (Ord a,QA a) => Q a -> Q a -> Q Bool
gt a b = expToQ $ AppE Gt $ qToExp $ pair a b

(>) :: (Ord a,QA a) => Q a -> Q a -> Q Bool
(>) = gt

min :: forall a. (Ord a, QA a) => Q a -> Q a -> Q a
min a b = expToQ $ AppE Min $ qToExp $ pair a b

max :: forall a. (Ord a, QA a) => Q a -> Q a -> Q a
max a b = expToQ $ AppE Max $ qToExp $ pair a b

-- * Conditionals
-- | Boolean fold
-- | It's first argument is used in the case of False
-- | It's second argument is used in the case of True
-- | The third argument is the boolean
bool :: (QA a) => Q a -> Q a -> Q Bool -> Q a
bool f t b = cond b t f

cond :: forall a. (QA a) => Q Bool -> Q a -> Q a -> Q a
cond c a b = expToQ $ AppE Cond $ qToExp $ pair c (pair a b)

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
cons a as = expToQ $ AppE Cons $ qToExp $ pair a as

(<|) :: (QA a) => Q a -> Q [a] -> Q [a]
(<|) = cons

snoc :: forall a. (QA a) => Q [a] -> Q a -> Q [a]
snoc as a = expToQ $ AppE Snoc $ qToExp $ pair as a

(|>) :: (QA a) => Q [a] -> Q a -> Q [a]
(|>) = snoc

singleton :: (QA a) => Q a -> Q [a]
singleton a = cons a nil

-- * List Operations

head :: forall a. (QA a) => Q [a] -> Q a
head as = expToQ $ AppE Head $ qToExp as 

tail :: forall a. (QA a) => Q [a] -> Q [a]
tail as = expToQ $ AppE Tail $ qToExp as 

take :: forall a. (QA a) => Q Integer -> Q [a] -> Q [a]
take i as = expToQ $ AppE Take $ qToExp $ pair i as 

drop :: forall a. (QA a) => Q Integer -> Q [a] -> Q [a]
drop i as = expToQ $ AppE Drop $ qToExp $ pair i as

map :: forall a b. (QA a, QA b) => (Q a -> Q b) ->  Q [a] -> Q [b]
map f as = expToQ $ AppE Map $ PairE (toLam1 f) (qToExp as)

{-
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

lookup :: (QA a,QA b,Eq a) => Q a -> Q [(a, b)] -> Q (Maybe b)
lookup a  = listToMaybe . map snd . filter ((a ==) . fst)

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
-}
pair :: forall a b. (QA a, QA b) => Q a -> Q b -> Q (a, b)
pair a b = expToQ (PairE (qToExp a) (qToExp b))
{-
-- * Conversions between numeric types

integerToDouble :: Q Integer -> Q Double
integerToDouble (Q a) = Q (AppE1 IntegerToDouble a DoubleT)

-- * Convert Haskell values into DB queries

toQ   :: forall a. (QA a) => a -> Q a
toQ c = Q (convert (toNorm c))

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

$(generateDeriveTupleQARange   5 7)
$(generateDeriveTupleTARange   3 7)
$(generateDeriveTupleViewRange 3 7)

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

-} -}
