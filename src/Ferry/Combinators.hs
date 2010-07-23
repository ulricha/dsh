{-# LANGUAGE TemplateHaskell #-}

module Ferry.Combinators where

import Ferry.Data
import Ferry.Class
import Ferry.Combinators.Tuples

import Prelude (Eq, Ord, Num, Bool, Int, (.))

-- * Unit

unit :: Q ()
unit = Q UnitE

-- * List Constraction

nil :: (QA a) => Q [a]
nil = Q (ListE [])

cons :: (QA a) => Q a -> Q [a] -> Q [a]
cons (Q a) (Q as) = Q (AppE (AppE (VarE "cons") a) as)

-- * List Operations

head :: (QA a) => Q [a] -> Q a
head (Q as) = Q (AppE (VarE "head") as)

tail :: (QA a) => Q [a] -> Q [a]
tail (Q as) = Q (AppE (VarE "tail") as)

take :: (QA a) => Q Int -> Q [a] -> Q [a]
take (Q i) (Q as) = Q (AppE (AppE (VarE "take") i) as)

drop :: (QA a) => Q Int -> Q [a] -> Q [a]
drop (Q i) (Q as) = Q (AppE (AppE (VarE "drop") i) as)

map :: (QA a, QA b) => (Q a -> Q b) ->  Q [a] -> Q [b]
map f (Q as) = Q (AppE (AppE (VarE "map") (FuncE (forget . f . Q))) as)

-- | Corresponds to @(++)@.
append :: (QA a) => Q [a] -> Q [a] -> Q [a]
append (Q as) (Q bs) = Q (AppE (AppE (VarE "append") as) bs)

filter :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q [a]
filter f (Q as) = Q (AppE (AppE (VarE "filter") (FuncE (forget . f . Q))) as)

groupWith :: (Ord b, QA a, QA b) => (Q a -> Q b) -> Q [a] -> Q [[a]]
groupWith f (Q as) = Q (AppE (AppE (VarE "groupWith") (FuncE (forget . f . Q))) as)

sortWith :: (Ord b, QA a, QA b) => (Q a -> Q b) -> Q [a] -> Q [a]
sortWith f (Q as) = Q (AppE (AppE (VarE "sortWith") (FuncE (forget . f . Q))) as)

the :: (Eq a, QA a) => Q [a] -> Q a
the (Q as) = Q (AppE (VarE "the") as)

last :: (QA a) => Q [a] -> Q a
last (Q as) = Q (AppE (VarE "last") as)

init :: (QA a) => Q [a] -> Q [a]
init (Q as) = Q (AppE (VarE "init") as)

null :: (QA a) => Q [a] -> Q Bool
null (Q as) = Q (AppE (VarE "null") as)

length :: (QA a) => Q [a] -> Q Int
length (Q as) = Q (AppE (VarE "length") as)

-- | Corresponds to @(!!)@.
index :: (QA a) => Q [a] -> Q Int -> Q a
index (Q as) (Q i) = Q (AppE (AppE (VarE "index") as) i)

reverse :: (QA a) => Q [a] -> Q [a]
reverse (Q as) = Q (AppE (VarE "reverse") as)


-- * Special folds

and       :: Q [Bool] -> Q Bool
and (Q as) = Q (AppE (VarE "and") as)

or        :: Q [Bool] -> Q Bool
or (Q as) = Q (AppE (VarE "or") as)

any       :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q Bool
any f (Q as) = Q (AppE (AppE (VarE "any") (FuncE (forget . f . Q))) as)

all       :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q Bool
all f (Q as) = Q (AppE (AppE (VarE "all") (FuncE (forget . f . Q))) as)

sum       :: (QA a, Num a) => Q [a] -> Q a
sum (Q as) = Q (AppE (VarE "sum") as)

product   :: (QA a, Num a) => Q [a] -> Q a
product (Q as) = Q (AppE (VarE "product") as)

concat    :: (QA a) => Q [[a]] -> Q [a]
concat (Q as) = Q (AppE (VarE "concat") as)

concatMap :: (QA a, QA b) => (Q a -> Q [b]) -> Q [a] -> Q [b]
concatMap f (Q as) = Q (AppE (AppE (VarE "concatMap") (FuncE (forget . f . Q))) as)

maximum   :: (QA a, Ord a) => Q [a] -> Q a
maximum (Q as) = Q (AppE (VarE "maximum") as)

minimum   :: (QA a, Ord a) => Q [a] -> Q a
minimum (Q as) = Q (AppE (VarE "minimum") as)

replicate :: (QA a) => Q Int -> Q a -> Q [a]
replicate (Q i) (Q a) = Q (AppE (AppE (VarE "replicate") i) a)


-- * Sublists

splitAt   :: (QA a) => Q Int -> Q [a] -> Q ([a], [a])
splitAt (Q i) (Q as) = Q (AppE (AppE (VarE "splitAt") i) as)

takeWhile :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q [a]
takeWhile f (Q as) = Q (AppE (AppE (VarE "takeWhile") (FuncE (forget . f . Q))) as)

dropWhile :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q [a]
dropWhile f (Q as) = Q (AppE (AppE (VarE "droptWhile") (FuncE (forget . f . Q))) as)

span      :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q ([a],[a])
span f (Q as) = Q (AppE (AppE (VarE "span") (FuncE (forget . f . Q))) as)

break     :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q ([a],[a])
break f (Q as) = Q (AppE (AppE (VarE "break") (FuncE (forget . f . Q))) as)

-- * Searching Lists

elem      :: (QA a, Eq a) => Q a -> Q [a] -> Q Bool
elem (Q a) (Q as) = Q (AppE (AppE (VarE "elem") a) as)

notElem   :: (QA a, Eq a) => Q a -> Q [a] -> Q Bool
notElem (Q a) (Q as) = Q (AppE (AppE (VarE "notElem") a) as)

-- * Zipping and Unzipping Lists

zip       :: (QA a, QA b) => Q [a] -> Q [b] -> Q [(a,b)]
zip (Q as) (Q bs) = Q (AppE (AppE (VarE "zip") as) bs)

zipWith   :: (QA a, QA b, QA c) => (Q a -> Q b -> Q c) -> Q [a] -> Q [b] -> Q [c]
zipWith f (Q as) (Q bs) =
  let f1 = \a b -> forget (f (Q a) (Q b))
      f2 = \a -> FuncE (\b -> f1 a b)
  in  Q (AppE (AppE (AppE (VarE "zipWith") (FuncE f2)) as) bs)

unzip     :: (QA a, QA b) => Q [(a,b)] -> Q ([a], [b])
unzip (Q as) = Q (AppE (VarE "unzip") as)

-- * Tuple Projection Functions

fst :: (QA a, QA b) => Q (a,b) -> Q a
fst = proj_2_1

snd :: (QA a, QA b) => Q (a,b) -> Q b 
snd = proj_2_2


-- * Tuple Construction

pair :: (QA a, QA b) => Q a -> Q b -> Q (a, b)
pair = tuple_2


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
