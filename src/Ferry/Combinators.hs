{-# Options -fno-warn-incomplete-patterns #-}

module Ferry.Combinators where

import Ferry.Data
import Ferry.Class
import Ferry.TH
import Ferry.Evaluate

import Database.HDBC

import Prelude (Eq, Ord, Num, Bool, Int, IO, return , (>>=), (.))

-- * Unit

unit :: Q ()
unit = Q UnitE

-- * Boolean logic

not :: Q Bool -> Q Bool
not (Q b) = Q (AppE1 Not b)

(&&) :: Q Bool -> Q Bool -> Q Bool
(&&) (Q a) (Q b) = Q (AppE2 Conj a b)

(||) :: Q Bool -> Q Bool -> Q Bool
(||) (Q a) (Q b) = Q (AppE2 Disj a b)

-- * Equality and Ordering

eq :: (Eq a,QA a) => Q a -> Q a -> Q Bool
eq (Q a) (Q b) = Q (AppE2 Equ a b)

(==) :: (Eq a,QA a) => Q a -> Q a -> Q Bool
(==) = eq

neq :: (Eq a,QA a) => Q a -> Q a -> Q Bool
neq a b = not (eq a b)

(/=) :: (Eq a,QA a) => Q a -> Q a -> Q Bool
(/=) = neq

lt :: (Ord a,QA a) => Q a -> Q a -> Q Bool
lt (Q a) (Q b) = Q (AppE2 Lt a b)

(<) :: (Ord a,QA a) => Q a -> Q a -> Q Bool
(<) = lt

lte :: (Ord a,QA a) => Q a -> Q a -> Q Bool
lte (Q a) (Q b) = Q (AppE2 Lte a b)

(<=) :: (Ord a,QA a) => Q a -> Q a -> Q Bool
(<=) = lte

gte :: (Ord a,QA a) => Q a -> Q a -> Q Bool
gte (Q a) (Q b) = Q (AppE2 Gte a b)

(>=) :: (Ord a,QA a) => Q a -> Q a -> Q Bool
(>=) = gte

gt :: (Ord a,QA a) => Q a -> Q a -> Q Bool
gt (Q a) (Q b) = Q (AppE2 Gt a b)

(>) :: (Ord a,QA a) => Q a -> Q a -> Q Bool
(>) = gt


-- * Conditionals
    
bool :: (QA a) => Q a -> Q a -> Q Bool -> Q a
bool a b c = c ? (a,b)

(?) :: (QA a) => Q Bool -> (Q a,Q a) -> Q a
(?) (Q c) (Q a,Q b) = Q (AppE3 Cond c a b)

-- * List Constraction

nil :: (QA a) => Q [a]
nil = Q (ListE [])

empty :: (QA a) => Q [a]
empty = nil

cons :: (QA a) => Q a -> Q [a] -> Q [a]
cons (Q a) (Q as) = Q (AppE2 Cons a as)

(<|) :: (QA a) => Q a -> Q [a] -> Q [a]
(<|) = cons

snoc :: (QA a) => Q [a] -> Q a -> Q [a]
snoc (Q as) (Q a) = Q (AppE2 Snoc as a)

(|>) :: (QA a) => Q [a] -> Q a -> Q [a]
(|>) = snoc

singleton :: (QA a) => Q a -> Q [a]
singleton a = cons a nil

-- * List Operations

head :: (QA a) => Q [a] -> Q a
head (Q as) = Q (AppE1 Head as)

tail :: (QA a) => Q [a] -> Q [a]
tail (Q as) = Q (AppE1 Tail as)

take :: (QA a) => Q Int -> Q [a] -> Q [a]
take (Q i) (Q as) = Q (AppE2 Take i as)

drop :: (QA a) => Q Int -> Q [a] -> Q [a]
drop (Q i) (Q as) = Q (AppE2 Drop i as)

map :: (QA a, QA b) => (Q a -> Q b) ->  Q [a] -> Q [b]
map f (Q as) = Q (AppE2 Map (LamE (forget . f . Q)) as)

append :: (QA a) => Q [a] -> Q [a] -> Q [a]
append (Q as) (Q bs) = Q (AppE2 Append as bs)

(><) :: (QA a) => Q [a] -> Q [a] -> Q [a]
(><) = append

filter :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q [a]
filter f (Q as) = Q (AppE2 Filter (LamE (forget . f . Q)) as)

groupWith :: (Ord b, QA a, QA b) => (Q a -> Q b) -> Q [a] -> Q [[a]]
groupWith f (Q as) = Q (AppE2 GroupWith (LamE (forget . f . Q)) as)

sortWith :: (Ord b, QA a, QA b) => (Q a -> Q b) -> Q [a] -> Q [a]
sortWith f (Q as) = Q (AppE2 SortWith (LamE (forget . f . Q)) as)

the :: (Eq a, QA a) => Q [a] -> Q a
the (Q as) = Q (AppE1 The as)

last :: (QA a) => Q [a] -> Q a
last (Q as) = Q (AppE1 Last as)

init :: (QA a) => Q [a] -> Q [a]
init (Q as) = Q (AppE1 Init as)

null :: (QA a) => Q [a] -> Q Bool
null (Q as) = Q (AppE1 Null as)

length :: (QA a) => Q [a] -> Q Int
length (Q as) = Q (AppE1 Length as)

index :: (QA a) => Q [a] -> Q Int -> Q a
index (Q as) (Q i) = Q (AppE2 Index as i)

(!) :: (QA a) => Q [a] -> Q Int -> Q a
(!) = index

reverse :: (QA a) => Q [a] -> Q [a]
reverse (Q as) = Q (AppE1 Reverse as)


-- * Special folds

and       :: Q [Bool] -> Q Bool
and (Q as) = Q (AppE1 And as)

or        :: Q [Bool] -> Q Bool
or (Q as) = Q (AppE1 Or as)

any       :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q Bool
any f (Q as) = Q (AppE2 Any (LamE (forget . f . Q)) as)

all       :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q Bool
all f (Q as) = Q (AppE2 All (LamE (forget . f . Q)) as)

sum       :: (QA a, Num a) => Q [a] -> Q a
sum (Q as) = Q (AppE1 Sum as)

product   :: (QA a, Num a) => Q [a] -> Q a
product (Q as) = Q (AppE1 Product as)

concat    :: (QA a) => Q [[a]] -> Q [a]
concat (Q as) = Q (AppE1 Concat as)

concatMap :: (QA a, QA b) => (Q a -> Q [b]) -> Q [a] -> Q [b]
concatMap f as = concat (map f as)

maximum   :: (QA a, Ord a) => Q [a] -> Q a
maximum (Q as) = Q (AppE1 Maximum as)

minimum   :: (QA a, Ord a) => Q [a] -> Q a
minimum (Q as) = Q (AppE1 Minimum as)

replicate :: (QA a) => Q Int -> Q a -> Q [a]
replicate (Q i) (Q a) = Q (AppE2 Replicate i a)


-- * Sublists

splitAt   :: (QA a) => Q Int -> Q [a] -> Q ([a], [a])
splitAt (Q i) (Q as) = Q (AppE2 SplitAt i as)

takeWhile :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q [a]
takeWhile f (Q as) = Q (AppE2 TakeWhile (LamE (forget . f . Q)) as)

dropWhile :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q [a]
dropWhile f (Q as) = Q (AppE2 DropWhile (LamE (forget . f . Q)) as)

span      :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q ([a],[a])
span f (Q as) = Q (AppE2 Span (LamE (forget . f . Q)) as)

break     :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q ([a],[a])
break f (Q as) = Q (AppE2 Break (LamE (forget . f . Q)) as)

-- * Searching Lists

elem      :: (QA a, Eq a) => Q a -> Q [a] -> Q Bool
elem (Q a) (Q as) = Q (AppE2 Elem a as)

notElem   :: (QA a, Eq a) => Q a -> Q [a] -> Q Bool
notElem a as = not (elem a as)

-- * Zipping and Unzipping Lists

zip       :: (QA a, QA b) => Q [a] -> Q [b] -> Q [(a,b)]
zip (Q as) (Q bs) = Q (AppE2 Zip as bs)

zipWith   :: (QA a, QA b, QA c) => (Q a -> Q b -> Q c) -> Q [a] -> Q [b] -> Q [c]
zipWith f (Q as) (Q bs) =
  let f1 = \a b -> forget (f (Q a) (Q b))
      f2 = \a -> LamE (\b -> f1 a b)
  in  Q (AppE3 ZipWith (LamE f2) as bs)

unzip     :: (QA a, QA b) => Q [(a,b)] -> Q ([a], [b])
unzip (Q as) = Q (AppE1 Unzip as)

-- * "Set" operations

nub :: Eq a => Q [a] -> Q [a]
nub (Q as) = Q (AppE1 Nub as) 


-- * Tuple Projection Functions

fst :: (QA a, QA b) => Q (a,b) -> Q a
fst (Q a) = Q (AppE1 Fst a)

snd :: (QA a, QA b) => Q (a,b) -> Q b
snd (Q a) = Q (AppE1 Snd a)

-- * Convert Haskell values into DB queries and back

toQ   :: (QA a) => a -> Q a
toQ = Q . normToExp . toNorm

fromQ :: (QA a, IConnection conn) => conn -> Q a -> IO a
fromQ c (Q a) = evaluate c a >>= (return . fromNorm)

infixl 9 !
infixr 5 ><, <|, |>
infix  4  ==, /=, <, <=, >=, >
infixr 3  &&
infixr 2  ||
infix  0 ?

-- 'QA', 'TA' and 'View' instances for tuples up to the defined length.

$(generateDeriveTupleQARange   3 16)
$(generateDeriveTupleTARange   3 16)
$(generateDeriveTupleViewRange 3 16)


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
