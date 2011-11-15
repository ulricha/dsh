module Database.DSH.Combinators where

import Database.DSH.Data

import Prelude (Eq, Ord, Num, Bool(..), Integer, Double)

-- * Unit

unit :: Q ()
unit = ToQ ()

-- * Boolean logic

false :: Q Bool
false = ToQ False

true :: Q Bool
true = ToQ True

not :: Q Bool -> Q Bool
not = NotQ

(&&) :: Q Bool -> Q Bool -> Q Bool
(&&) = ConjQ

(||) :: Q Bool -> Q Bool -> Q Bool
(||) = DisjQ

-- * Equality and Ordering

eq :: (Eq a,QA a) => Q a -> Q a -> Q Bool
eq = EquQ

(==) :: (Eq a,QA a) => Q a -> Q a -> Q Bool
(==) = eq

neq :: (Eq a,QA a) => Q a -> Q a -> Q Bool
neq a b = not (eq a b)

(/=) :: (Eq a,QA a) => Q a -> Q a -> Q Bool
(/=) = neq

lt :: (Ord a,QA a) => Q a -> Q a -> Q Bool
lt = LtQ

(<) :: (Ord a,QA a) => Q a -> Q a -> Q Bool
(<) = lt

lte :: (Ord a,QA a) => Q a -> Q a -> Q Bool
lte = LteQ

(<=) :: (Ord a,QA a) => Q a -> Q a -> Q Bool
(<=) = lte

gte :: (Ord a,QA a) => Q a -> Q a -> Q Bool
gte = GteQ

(>=) :: (Ord a,QA a) => Q a -> Q a -> Q Bool
(>=) = gte

gt :: (Ord a,QA a) => Q a -> Q a -> Q Bool
gt = GtQ

(>) :: (Ord a,QA a) => Q a -> Q a -> Q Bool
(>) = gt

min :: (Ord a,QA a) => Q a -> Q a -> Q a
min = MinQ

max :: (Ord a,QA a) => Q a -> Q a -> Q a
max = MaxQ

-- * Conditionals
-- | Boolean fold
-- | It's first argument is used in the case of False
-- | It's second argument is used in the case of True
-- | The third argument is the boolean
bool :: (QA a) => Q a -> Q a -> Q Bool -> Q a
bool f t b = cond b t f

cond :: (QA a) => Q Bool -> Q a -> Q a -> Q a
cond = CondQ

(?) :: (QA a) => Q Bool -> (Q a,Q a) -> Q a
(?) c (a,b) = cond c a b

-- * List Construction

nil :: (QA a) => Q [a]
nil = ToQ []

empty :: (QA a) => Q [a]
empty = nil

cons :: (QA a) => Q a -> Q [a] -> Q [a]
cons = ConsQ

(<|) :: (QA a) => Q a -> Q [a] -> Q [a]
(<|) = cons

snoc :: (QA a) => Q [a] -> Q a -> Q [a]
snoc = SnocQ

(|>) :: (QA a) => Q [a] -> Q a -> Q [a]
(|>) = snoc

singleton :: (QA a) => Q a -> Q [a]
singleton a = cons a nil

-- * List Operations

head :: (QA a) => Q [a] -> Q a
head = HeadQ

tail :: (QA a) => Q [a] -> Q [a]
tail = TailQ

take :: (QA a) => Q Integer -> Q [a] -> Q [a]
take = TakeQ

drop :: (QA a) => Q Integer -> Q [a] -> Q [a]
drop = DropQ

map :: (QA a, QA b) => (Q a -> Q b) ->  Q [a] -> Q [b]
map = MapQ

append :: (QA a) => Q [a] -> Q [a] -> Q [a]
append = AppendQ

(><) :: (QA a) => Q [a] -> Q [a] -> Q [a]
(><) = append

filter :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q [a]
filter = FilterQ

groupWith :: (Ord b, QA a, QA b) => (Q a -> Q b) -> Q [a] -> Q [[a]]
groupWith = GroupWithQ

sortWith :: (Ord b, QA a, QA b) => (Q a -> Q b) -> Q [a] -> Q [a]
sortWith = SortWithQ

the :: (Eq a, QA a) => Q [a] -> Q a
the = TheQ

last :: (QA a) => Q [a] -> Q a
last = LastQ

init :: (QA a) => Q [a] -> Q [a]
init = InitQ

null :: (QA a) => Q [a] -> Q Bool
null = NullQ

length :: (QA a) => Q [a] -> Q Integer
length = LengthQ

index :: (QA a) => Q [a] -> Q Integer -> Q a
index = IndexQ

(!!) :: (QA a) => Q [a] -> Q Integer -> Q a
(!!) = index

reverse :: (QA a) => Q [a] -> Q [a]
reverse = ReverseQ


-- * Special folds

and       :: Q [Bool] -> Q Bool
and = AndQ

or        :: Q [Bool] -> Q Bool
or = OrQ

any       :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q Bool
any = AnyQ

all       :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q Bool
all = AllQ

sum       :: (QA a, Num a) => Q [a] -> Q a
sum = SumQ

concat    :: (QA a) => Q [[a]] -> Q [a]
concat = ConcatQ

concatMap :: (QA a, QA b) => (Q a -> Q [b]) -> Q [a] -> Q [b]
concatMap f as = concat (map f as)

maximum   :: (QA a, Ord a) => Q [a] -> Q a
maximum = MaximumQ

minimum   :: (QA a, Ord a) => Q [a] -> Q a
minimum = MinimumQ

-- * Sublists

splitAt   :: (QA a) => Q Integer -> Q [a] -> Q ([a],[a])
splitAt = SplitAtQ

takeWhile :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q [a]
takeWhile = TakeWhileQ

dropWhile :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q [a]
dropWhile = DropWhileQ

span      :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q ([a],[a])
span = SpanQ

break     :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q ([a],[a])
break = BreakQ


-- * Searching Lists

elem :: (Eq a, QA a) => Q a -> Q [a] -> Q Bool
elem a as = (null (filter (a ==) as)) ? (false,true)

notElem :: (Eq a, QA a) => Q a -> Q [a] -> Q Bool
notElem a as = not (elem a as)

-- lookup :: (QA a,QA b,Eq a) => Q a -> Q [(a, b)] -> Q (Maybe b)
-- lookup a  = listToMaybe . map snd . filter ((a ==) . fst)

-- * Zipping and Unzipping Lists

zip       :: (QA a, QA b) => Q [a] -> Q [b] -> Q [(a,b)]
zip = ZipQ

zipWith   :: (QA a, QA b, QA c) => (Q a -> Q b -> Q c) -> Q [a] -> Q [b] -> Q [c]
zipWith = ZipWithQ

unzip     :: (QA a, QA b) => Q [(a,b)] -> Q ([a], [b])
unzip = UnzipQ

-- * "Set" operations

nub :: (Eq a,QA a) => Q [a] -> Q [a]
nub = NubQ


-- * Tuple Projection Functions

fst :: (QA a, QA b) => Q (a,b) -> Q a
fst = FstQ

snd :: (QA a, QA b) => Q (a,b) -> Q b
snd = SndQ


-- * Conversions between numeric types

integerToDouble :: Q Integer -> Q Double
integerToDouble = IntegerToDoubleQ

-- * Convert Haskell values into DB queries

toQ   :: (QA a) => a -> Q a
toQ = ToQ

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
