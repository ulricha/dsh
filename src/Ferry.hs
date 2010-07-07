{-# LANGUAGE GADTs, FlexibleInstances #-}

-- |
-- This module is intended to be imported @qualified@, to avoid name clashes
-- with "Prelude" functions. For example:
--
-- > import qualified Ferry as Q
-- > import Ferry (Q)


module Ferry
  (
    Q
  , QA (toQ, fromQ)

  , nil
  , cons
  , groupWith
  , sortWith
  , the

    -- * List operations
  , map
  , append
  , filter
  , head
  , last
  , tail
  , init
  , null
  , length
  , index
  , reverse
  , replicate

    -- * Special folds
  , and
  , or
  , any
  , all
  , sum
  , product
  , concat
  , concatMap
  , maximum
  , minimum

    -- * Sublists
  , take
  , drop
  , splitAt
  , takeWhile
  , dropWhile
  , span
  , break

    -- * Searching lists
  , elem
  , notElem

    -- * Zipping and unzipping lists
  , zip
  , zipWith
  , unzip

    -- * Missing functions
    -- $missing
  )
  where

import qualified GHC.Exts as P (groupWith, sortWith, the)
import qualified Prelude as P
import Prelude ( Eq(..), Ord(..), Num(..),Show(..),
                 Bool, Int, Char,
                 (.), ($), (!!), (++),
                 fromIntegral,
               )


 
data Q a where
  ToQ :: (QA a) => a -> Q a

  Eq :: (Eq a,QA a) => Q a -> Q a -> Q Bool

  Add :: Q Int -> Q Int -> Q Int
  Mul :: Q Int -> Q Int -> Q Int
  Neg :: Q Int -> Q Int
  Abs :: Q Int -> Q Int
  Sgn :: Q Int -> Q Int

  Nil       :: (QA a) => Q [a]
  Cons      :: (QA a) => Q a -> Q [a] -> Q [a]

  Head      :: (QA a) => Q [a] -> Q a
  Tail      :: (QA a) => Q [a] -> Q [a]
  The       :: (Eq a, QA a) => Q [a] -> Q a
  Last      :: (QA a) => Q [a] -> Q a
  Init      :: (QA a) => Q [a] -> Q [a]
  Null      :: (QA a) => Q [a] -> Q Bool
  Length    :: (QA a) => Q [a] -> Q Int
  Index     :: (QA a) => Q [a] -> Q Int -> Q a
  Reverse   :: (QA a) => Q [a] -> Q [a]

  Take      :: (QA a) => Q Int -> Q [a] -> Q [a]
  Drop      :: (QA a) => Q Int -> Q [a] -> Q [a]
  Map       :: (QA a, QA b) => (Q a -> Q b) ->  Q [a] -> Q [b]
  Append    :: (QA a) => Q [a] -> Q [a] -> Q [a]
  Filter    :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q [a]
  GroupWith :: (Ord b, QA a, QA b) => (Q a -> Q b) -> Q [a] -> Q [[a]]
  SortWith  :: (Ord b, QA a, QA b) => (Q a -> Q b) -> Q [a] -> Q [a]

  And       :: Q [Bool] -> Q Bool
  Or        :: Q [Bool] -> Q Bool
  Any       :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q Bool
  All       :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q Bool
  Sum       :: (QA a, Num a) => Q [a] -> Q a
  Product   :: (QA a, Num a) => Q [a] -> Q a
  Concat    :: (QA a) => Q [[a]] -> Q [a]
  ConcatMap :: (QA a, QA b) => (Q a -> Q [b]) -> Q [a] -> Q [b]
  Maximum   :: (QA a, Ord a) => Q [a] -> Q a
  Minimum   :: (QA a, Ord a) => Q [a] -> Q a

  Replicate :: (QA a) => Q Int -> Q a -> Q [a]

  SplitAt   :: (QA a) => Q Int -> Q [a] -> Q ([a], [a])
  TakeWhile :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q [a]
  DropWhile :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q [a]

  Span      :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q ([a],[a])
  Break     :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q ([a],[a])

  Elem      :: (QA a, Eq a) => Q a -> Q [a] -> Q Bool
  NotElem   :: (QA a, Eq a) => Q a -> Q [a] -> Q Bool

  Zip       :: (QA a, QA b) => Q [a] -> Q [b] -> Q [(a,b)]
  ZipWith   :: (QA a, QA b, QA c) => (Q a -> Q b -> Q c) -> Q [a] -> Q [b] -> Q [c]
  Unzip     :: (QA a, QA b) => Q [(a,b)] -> Q ([a], [b])

nil :: (QA a) => Q [a]
nil = Nil

cons :: (QA a) => Q a -> Q [a] -> Q [a]
cons = Cons

head :: (QA a) => Q [a] -> Q a
head = Head

tail :: (QA a) => Q [a] -> Q [a]
tail = Tail

take :: (QA a) => Q Int -> Q [a] -> Q [a]
take = Take

drop :: (QA a) => Q Int -> Q [a] -> Q [a]
drop = Drop

map :: (QA a, QA b) => (Q a -> Q b) ->  Q [a] -> Q [b]
map = Map

-- | Corresponds to @(++)@.
append :: (QA a) => Q [a] -> Q [a] -> Q [a]
append = Append

filter :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q [a]
filter = Filter

groupWith :: (Ord b, QA a, QA b) => (Q a -> Q b) -> Q [a] -> Q [[a]]
groupWith = GroupWith

sortWith :: (Ord b, QA a, QA b) => (Q a -> Q b) -> Q [a] -> Q [a]
sortWith = SortWith

the :: (Eq a, QA a) => Q [a] -> Q a
the = The

last :: (QA a) => Q [a] -> Q a
last = Last

init :: (QA a) => Q [a] -> Q [a]
init = Init

null :: (QA a) => Q [a] -> Q Bool
null = Null

length :: (QA a) => Q [a] -> Q Int
length = Length

-- | Corresponds to @(!!)@.
index :: (QA a) => Q [a] -> Q Int -> Q a
index = Index

reverse :: (QA a) => Q [a] -> Q [a]
reverse = Reverse


-- Special folds

and       :: Q [Bool] -> Q Bool
and = And

or        :: Q [Bool] -> Q Bool
or = Or

any       :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q Bool
any = Any

all       :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q Bool
all = All

sum       :: (QA a, Num a) => Q [a] -> Q a
sum = Sum

product   :: (QA a, Num a) => Q [a] -> Q a
product = Product

concat    :: (QA a) => Q [[a]] -> Q [a]
concat = Concat

concatMap :: (QA a, QA b) => (Q a -> Q [b]) -> Q [a] -> Q [b]
concatMap = ConcatMap

maximum   :: (QA a, Ord a) => Q [a] -> Q a
maximum = Maximum

minimum   :: (QA a, Ord a) => Q [a] -> Q a
minimum = Minimum

replicate :: (QA a) => Q Int -> Q a -> Q [a]
replicate = Replicate


-- Sublists

splitAt   :: (QA a) => Q Int -> Q [a] -> Q ([a], [a])
splitAt = SplitAt

takeWhile :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q [a]
takeWhile = TakeWhile

dropWhile :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q [a]
dropWhile = DropWhile

span      :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q ([a],[a])
span = Span

break     :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q ([a],[a])
break = Break

elem      :: (QA a, Eq a) => Q a -> Q [a] -> Q Bool
elem = Elem

notElem   :: (QA a, Eq a) => Q a -> Q [a] -> Q Bool
notElem = NotElem

zip       :: (QA a, QA b) => Q [a] -> Q [b] -> Q [(a,b)]
zip = Zip

zipWith   :: (QA a, QA b, QA c) => (Q a -> Q b -> Q c) -> Q [a] -> Q [b] -> Q [c]
zipWith = ZipWith

unzip     :: (QA a, QA b) => Q [(a,b)] -> Q ([a], [b])
unzip = Unzip


class QA a where
  toQ :: a -> Q a
  toQ = ToQ

  fromQ :: Q a -> a


instance QA Bool where
  fromQ q = case q of
             ToQ a -> a
             Head as -> P.head (fromQ as)
             The as -> P.the (fromQ as)
             Eq b1 b2 -> (fromQ b1) == (fromQ b2)
             Last as -> P.last (fromQ as)
             Null as -> P.null (fromQ as)
             Index as i -> (fromQ as) !! (fromQ i)
             And as -> P.and (fromQ as)
             Or as -> P.or (fromQ as)
             Any f as -> P.any (fromQ . f . toQ) (fromQ as)
             All f as -> P.all (fromQ . f . toQ) (fromQ as)
             Sum as -> P.sum (fromQ as)
             Product as -> P.product (fromQ as)
             Maximum as -> P.maximum (fromQ as)
             Minimum as -> P.minimum (fromQ as)
             Elem a as -> P.elem (fromQ a) (fromQ as)
             NotElem a as -> P.notElem (fromQ a) (fromQ as)


instance QA Int where
  fromQ q = case q of
             ToQ a -> a
             Head as -> P.head (fromQ as)
             The as -> P.the (fromQ as)
             Add i1 i2 -> (fromQ i1) + (fromQ i2)
             Mul i1 i2 -> (fromQ i1) + (fromQ i2)
             Neg i1 -> P.negate (fromQ i1)
             Abs i1 -> P.abs (fromQ i1)
             Sgn i1 -> P.signum (fromQ i1)
             Last as -> P.last (fromQ as)
             Length as -> P.length (fromQ as)
             Index as i -> (fromQ as) !! (fromQ i)
             Sum as -> P.sum (fromQ as)
             Product as -> P.product (fromQ as)
             Maximum as -> P.maximum (fromQ as)
             Minimum as -> P.minimum (fromQ as)


instance QA Char where
  fromQ q = case q of
             ToQ a -> a
             Head as -> P.head (fromQ as)
             The as -> P.the (fromQ as)
             Last as -> P.last (fromQ as)
             Index as i -> (fromQ as) !! (fromQ i)
             Sum as -> P.sum (fromQ as)
             Product as -> P.product (fromQ as)
             Maximum as -> P.maximum (fromQ as)
             Minimum as -> P.minimum (fromQ as)


instance QA a => QA [a] where
  fromQ q = case q of
             ToQ a -> a
             Nil   -> []
             Cons a as -> (fromQ a) : (fromQ as)
             Head as -> P.head (fromQ as)
             Tail as -> P.tail (fromQ as)
             Take i as -> P.take (fromQ i) (fromQ as)
             Drop i as -> P.drop (fromQ i) (fromQ as)
             Map f as -> P.map (fromQ . f . toQ) (fromQ as)
             Append as bs -> (fromQ as) ++ (fromQ bs)
             Filter f as -> P.filter (fromQ . f . toQ) (fromQ as)
             Zip as bs -> P.zip (fromQ as) (fromQ bs)
             GroupWith f as -> P.groupWith (fromQ . f . toQ) (fromQ as)
             SortWith f as -> P.sortWith (fromQ . f . toQ) (fromQ as)
             The as -> P.the (fromQ as)
             Last as -> P.last (fromQ as)
             Init as -> P.init (fromQ as)
             Index as i -> (fromQ as) !! (fromQ i)
             Reverse as -> P.reverse (fromQ as)
             Sum as -> P.sum (fromQ as)
             Product as -> P.product (fromQ as)
             Maximum as -> P.maximum (fromQ as)
             Minimum as -> P.minimum (fromQ as)
             Concat ass -> P.concat (fromQ ass)
             ConcatMap f as -> P.concatMap (fromQ . f . toQ) (fromQ as)
             Replicate i a -> P.replicate (fromQ i) (fromQ a)
             TakeWhile f as -> P.takeWhile (fromQ . f . toQ) (fromQ as)
             DropWhile f as -> P.dropWhile (fromQ . f . toQ) (fromQ as)
             ZipWith f as bs -> P.zipWith (\a b -> fromQ $ f (toQ a) (toQ b)) (fromQ as) (fromQ bs)


instance (QA a,QA b) => QA (a,b) where
  fromQ q = case q of
             ToQ a -> a
             Head as -> P.head (fromQ as)
             The as -> P.the (fromQ as)
             Last as -> P.last (fromQ as)
             Unzip as -> P.unzip (fromQ as)
             Index as i -> (fromQ as) !! (fromQ i)
             Sum as -> P.sum (fromQ as)
             Product as -> P.product (fromQ as)
             Maximum as -> P.maximum (fromQ as)
             Minimum as -> P.minimum (fromQ as)
             SplitAt i as -> P.splitAt (fromQ i) (fromQ as)
             Span f as -> P.span (fromQ . f . toQ) (fromQ as)
             Break f as -> P.break (fromQ . f . toQ) (fromQ as)


instance Show (Q a) where

instance Eq (Q Int) where

instance Num (Q Int) where
  (+) e1 e2 = Add e1 e2
  (*) e1 e2 = Mul e1 e2
  abs e1 = Abs e1
  negate e1 = Neg e1
  fromInteger i = ToQ (fromIntegral i)
  signum = Sgn


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
