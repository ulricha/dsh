module Database.DSH.Combinators where

import Database.DSH.Data
import Database.DSH.TH

import Prelude (Eq, Ord, Num, Bool(..), Integer, Double, Maybe, Either, undefined, ($), (.))

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

eq :: (QA a,Eq a) => Q a -> Q a -> Q Bool
eq (Q a) (Q b) = Q (AppE Equ (PairE a b))

(==) :: (QA a,Eq a) => Q a -> Q a -> Q Bool
(==) = eq

neq :: (QA a,Eq a) => Q a -> Q a -> Q Bool
neq a b = not (eq a b)

(/=) :: (QA a,Eq a) => Q a -> Q a -> Q Bool
(/=) = neq

lt :: (QA a,Ord a) => Q a -> Q a -> Q Bool
lt (Q a) (Q b) = Q (AppE Lt (PairE a b))

(<) :: (QA a,Ord a) => Q a -> Q a -> Q Bool
(<) = lt

lte :: (QA a,Ord a) => Q a -> Q a -> Q Bool
lte (Q a) (Q b) = Q (AppE Lte (PairE a b))

(<=) :: (QA a,Ord a) => Q a -> Q a -> Q Bool
(<=) = lte

gte :: (QA a,Ord a) => Q a -> Q a -> Q Bool
gte (Q a) (Q b) = Q (AppE Gte (PairE a b))

(>=) :: (QA a,Ord a) => Q a -> Q a -> Q Bool
(>=) = gte

gt :: (QA a,Ord a) => Q a -> Q a -> Q Bool
gt (Q a) (Q b) = Q (AppE Gt (PairE a b))

(>) :: (QA a,Ord a) => Q a -> Q a -> Q Bool
(>) = gt

min :: (QA a,Ord a) => Q a -> Q a -> Q a
min (Q a) (Q b) = Q (AppE Min (PairE a b))

max :: (QA a,Ord a) => Q a -> Q a -> Q a
max (Q a) (Q b) = Q (AppE Max (PairE a b))

-- * Conditionals

bool :: (QA a) => Q a -> Q a -> Q Bool -> Q a
bool f t b = cond b t f

cond :: (QA a) => Q Bool -> Q a -> Q a -> Q a
cond (Q c) (Q a) (Q b) = Q (AppE Cond (PairE c (PairE a b)))

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
left a = pairToEither (tuple (singleton a,nil))

right :: (QA a,QA b) => Q b -> Q (Either a b)
right a = pairToEither (tuple (nil,singleton a))

isLeft :: (QA a,QA b) => Q (Either a b) -> Q Bool
isLeft = null . snd . eitherToPair

isRight :: (QA a,QA b) => Q (Either a b) -> Q Bool
isRight = null . fst . eitherToPair

either :: (QA a,QA b,QA c) => (Q a -> Q c) -> (Q b -> Q c) -> Q (Either a b) -> Q c
either lf rf e = isLeft e ? ((lf . head . fst . eitherToPair) e,(rf . head . snd . eitherToPair) e)

lefts :: (QA a,QA b) => Q [Either a b] -> Q [a]
lefts = concatMap (fst . eitherToPair)

rights :: (QA a,QA b) => Q [Either a b] -> Q [b]
rights = concatMap (snd . eitherToPair)

partitionEithers :: (QA a,QA b) => Q [Either a b] -> Q ([a], [b])
partitionEithers es = tuple (lefts es,rights es)

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
take (Q i) (Q as) = Q (AppE Take (PairE i as))

drop :: (QA a) => Q Integer -> Q [a] -> Q [a]
drop (Q i) (Q as) = Q (AppE Drop (PairE i as))

map :: (QA a,QA b) => (Q a -> Q b) ->  Q [a] -> Q [b]
map f (Q as) = Q (AppE Map (PairE (LamE (toLam f)) as))

append :: (QA a) => Q [a] -> Q [a] -> Q [a]
append (Q as) (Q bs) = Q (AppE Concat (ListE [as,bs]))

(++) :: (QA a) => Q [a] -> Q [a] -> Q [a]
(++) = append

filter :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q [a]
filter f (Q as) = Q (AppE Filter (PairE (LamE (toLam f)) as))

groupWith :: (QA a,QA b,Ord b) => (Q a -> Q b) -> Q [a] -> Q [[a]]
groupWith f (Q as) = Q (AppE GroupWith (PairE (LamE (toLam f)) as))

sortWith :: (QA a,QA b,Ord b) => (Q a -> Q b) -> Q [a] -> Q [a]
sortWith f (Q as) = Q (AppE SortWith (PairE (LamE (toLam f)) as))

the :: (QA a,Eq a) => Q [a] -> Q a
the (Q as) = Q (AppE The as)

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

concat :: (QA a) => Q [[a]] -> Q [a]
concat (Q ass) = Q (AppE Concat ass)

concatMap :: (QA a,QA b) => (Q a -> Q [b]) -> Q [a] -> Q [b]
concatMap f as = concat (map f as)

maximum :: (QA a,Ord a) => Q [a] -> Q a
maximum (Q as) = Q (AppE Maximum as)

minimum :: (QA a,Ord a) => Q [a] -> Q a
minimum (Q as) = Q (AppE Minimum as)

-- * Sublists

splitAt :: (QA a) => Q Integer -> Q [a] -> Q ([a],[a])
splitAt (Q i) (Q as) = Q (AppE SplitAt (PairE i as))

takeWhile :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q [a]
takeWhile f (Q as) = Q (AppE TakeWhile (PairE (LamE (toLam f)) as))

dropWhile :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q [a]
dropWhile f (Q as) = Q (AppE DropWhile (PairE (LamE (toLam f)) as))

span :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q ([a],[a])
span f as = pair (takeWhile f as) (dropWhile f as)

break :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q ([a],[a])
break f = span (not . f)

-- * Searching Lists

elem :: (QA a,Eq a) => Q a -> Q [a] -> Q Bool
elem a as = null (filter (a ==) as) ? (false,true)

notElem :: (QA a,Eq a) => Q a -> Q [a] -> Q Bool
notElem a as = not (a `elem` as)

lookup :: (QA a,QA b,Eq a) => Q a -> Q [(a, b)] -> Q (Maybe b)
lookup a  = listToMaybe . map snd . filter ((a ==) . fst)

-- * Zipping and Unzipping Lists

zip :: (QA a,QA b) => Q [a] -> Q [b] -> Q [(a,b)]
zip (Q as) (Q bs) = Q (AppE Zip (PairE as bs))

zipWith :: (QA a,QA b,QA c) => (Q a -> Q b -> Q c) -> Q [a] -> Q [b] -> Q [c]
zipWith f as bs = map (\e -> f (fst e) (snd e)) (zip as bs)

unzip :: (QA a,QA b) => Q [(a,b)] -> Q ([a],[b])
unzip (Q as) = Q (AppE Unzip as)

-- * Set-oriented operations

nub :: (QA a,Eq a) => Q [a] -> Q [a]
nub (Q as) = Q (AppE Nub as)

-- * Tuple Projection Functions

fst :: (QA a,QA b) => Q (a,b) -> Q a
fst (Q e) = Q (AppE Fst e)

snd :: (QA a,QA b) => Q (a,b) -> Q b
snd (Q e) = Q (AppE Snd e)

pair :: (QA a,QA b) => Q a -> Q b -> Q (a,b)
pair (Q a) (Q b) = Q (PairE a b)

-- * Conversions between numeric types

integerToDouble :: Q Integer -> Q Double
integerToDouble (Q i) = Q (AppE IntegerToDouble i)

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
guard c = cond c (singleton unit) nil

infixl 9  !!
infixr 5  ++, <|, |>
infix  4  ==, /=, <, <=, >=, >
infixr 3  &&
infixr 2  ||
infix  0  ?

deriveTupleRangeQA 3 8

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

Zipping and unzipping lists:

> zip3
> zipWith3
> unzip3

-}
