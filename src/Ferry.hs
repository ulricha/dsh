{-# LANGUAGE GADTs, FlexibleInstances #-}

module Ferry
  (
    Q
  , QA
  , toQ
  , fromQ

  , nilQ
  , consQ
  , groupWithQ
  , sortWithQ
  , theQ

    -- * List operations
  , mapQ
  , appendQ
  , filterQ
  , headQ
  , lastQ
  , tailQ
  , initQ
  , nullQ
  , lengthQ
  , indexQ
  , reverseQ
  , replicateQ

    -- * Special folds
  , andQ
  , orQ
  , anyQ
  , allQ
  , sumQ
  , productQ
  , concatQ
  , concatMapQ
  , maximumQ
  , minimumQ

    -- * Sublists
  , takeQ
  , dropQ
  , splitAtQ
  , takeWhileQ
  , dropWhileQ
  , spanQ
  , breakQ

    -- * Searching lists
  , elemQ
  , notElemQ

    -- * Zipping and unzipping lists
  , zipQ
  , zipWithQ
  , unzipQ

    -- * Missing functions
    -- $missing
  )
  where

import GHC.Exts (groupWith, sortWith, the)

 
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

nilQ :: (QA a) => Q [a]
nilQ = Nil

consQ :: (QA a) => Q a -> Q [a] -> Q [a]
consQ = Cons

headQ :: (QA a) => Q [a] -> Q a
headQ = Head

tailQ :: (QA a) => Q [a] -> Q [a]
tailQ = Tail

takeQ :: (QA a) => Q Int -> Q [a] -> Q [a]
takeQ = Take

dropQ :: (QA a) => Q Int -> Q [a] -> Q [a]
dropQ = Drop

mapQ :: (QA a, QA b) => (Q a -> Q b) ->  Q [a] -> Q [b]
mapQ = Map

-- | Corresponds to @(++)@.
appendQ :: (QA a) => Q [a] -> Q [a] -> Q [a]
appendQ = Append

filterQ :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q [a]
filterQ = Filter

groupWithQ :: (Ord b, QA a, QA b) => (Q a -> Q b) -> Q [a] -> Q [[a]]
groupWithQ = GroupWith

sortWithQ :: (Ord b, QA a, QA b) => (Q a -> Q b) -> Q [a] -> Q [a]
sortWithQ = SortWith

theQ :: (Eq a, QA a) => Q [a] -> Q a
theQ = The

lastQ :: (QA a) => Q [a] -> Q a
lastQ = Last

initQ :: (QA a) => Q [a] -> Q [a]
initQ = Init

nullQ :: (QA a) => Q [a] -> Q Bool
nullQ = Null

lengthQ :: (QA a) => Q [a] -> Q Int
lengthQ = Length

-- | Corresponds to @(!!)@.
indexQ :: (QA a) => Q [a] -> Q Int -> Q a
indexQ = Index

reverseQ :: (QA a) => Q [a] -> Q [a]
reverseQ = Reverse


-- Special folds

andQ       :: Q [Bool] -> Q Bool
andQ = And

orQ        :: Q [Bool] -> Q Bool
orQ = Or

anyQ       :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q Bool
anyQ = Any

allQ       :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q Bool
allQ = All

sumQ       :: (QA a, Num a) => Q [a] -> Q a
sumQ = Sum

productQ   :: (QA a, Num a) => Q [a] -> Q a
productQ = Product

concatQ    :: (QA a) => Q [[a]] -> Q [a]
concatQ = Concat

concatMapQ :: (QA a, QA b) => (Q a -> Q [b]) -> Q [a] -> Q [b]
concatMapQ = ConcatMap

maximumQ   :: (QA a, Ord a) => Q [a] -> Q a
maximumQ = Maximum

minimumQ   :: (QA a, Ord a) => Q [a] -> Q a
minimumQ = Minimum

replicateQ :: (QA a) => Q Int -> Q a -> Q [a]
replicateQ = Replicate


-- Sublists

splitAtQ   :: (QA a) => Q Int -> Q [a] -> Q ([a], [a])
splitAtQ = SplitAt
takeWhileQ :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q [a]
takeWhileQ = TakeWhile
dropWhileQ :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q [a]
dropWhileQ = DropWhile

spanQ      :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q ([a],[a])
spanQ = Span
breakQ     :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q ([a],[a])
breakQ = Break

elemQ      :: (QA a, Eq a) => Q a -> Q [a] -> Q Bool
elemQ = Elem
notElemQ   :: (QA a, Eq a) => Q a -> Q [a] -> Q Bool
notElemQ = NotElem

zipQ       :: (QA a, QA b) => Q [a] -> Q [b] -> Q [(a,b)]
zipQ = Zip
zipWithQ   :: (QA a, QA b, QA c) => (Q a -> Q b -> Q c) -> Q [a] -> Q [b] -> Q [c]
zipWithQ = ZipWith
unzipQ     :: (QA a, QA b) => Q [(a,b)] -> Q ([a], [b])
unzipQ = Unzip


class QA a where
  toQ :: a -> Q a
  toQ = ToQ

  fromQ :: Q a -> a


instance QA Bool where
  fromQ q = case q of
             ToQ a -> a
             Head as -> head (fromQ as)
             The as -> the (fromQ as)
             Eq b1 b2 -> (fromQ b1) == (fromQ b2)
             Last as -> last (fromQ as)
             Null as -> null (fromQ as)
             Index as i -> (fromQ as) !! (fromQ i)
             And as -> and (fromQ as)
             Or as -> or (fromQ as)
             Any f as -> any (fromQ . f . toQ) (fromQ as)
             All f as -> all (fromQ . f . toQ) (fromQ as)
             Sum as -> sum (fromQ as)
             Product as -> product (fromQ as)
             Maximum as -> maximum (fromQ as)
             Minimum as -> minimum (fromQ as)
             Elem a as -> elem (fromQ a) (fromQ as)
             NotElem a as -> notElem (fromQ a) (fromQ as)


instance QA Int where
  fromQ q = case q of
             ToQ a -> a
             Head as -> head (fromQ as)
             The as -> the (fromQ as)
             Add i1 i2 -> (fromQ i1) + (fromQ i2)
             Mul i1 i2 -> (fromQ i1) + (fromQ i2)
             Neg i1 -> negate (fromQ i1)
             Abs i1 -> abs (fromQ i1)
             Sgn i1 -> signum (fromQ i1)
             Last as -> last (fromQ as)
             Length as -> length (fromQ as)
             Index as i -> (fromQ as) !! (fromQ i)
             Sum as -> sum (fromQ as)
             Product as -> product (fromQ as)
             Maximum as -> maximum (fromQ as)
             Minimum as -> minimum (fromQ as)


instance QA Char where
  fromQ q = case q of
             ToQ a -> a
             Head as -> head (fromQ as)
             The as -> the (fromQ as)
             Last as -> last (fromQ as)
             Index as i -> (fromQ as) !! (fromQ i)
             Sum as -> sum (fromQ as)
             Product as -> product (fromQ as)
             Maximum as -> maximum (fromQ as)
             Minimum as -> minimum (fromQ as)


instance QA a => QA [a] where
  fromQ q = case q of
             ToQ a -> a
             Nil   -> []
             Cons a as -> (fromQ a) : (fromQ as)
             Head as -> head (fromQ as)
             Tail as -> tail (fromQ as)
             Take i as -> take (fromQ i) (fromQ as)
             Drop i as -> drop (fromQ i) (fromQ as)
             Map f as -> map (fromQ . f . toQ) (fromQ as)
             Append as bs -> (fromQ as) ++ (fromQ bs)
             Filter f as -> filter (fromQ . f . toQ) (fromQ as)
             Zip as bs -> zip (fromQ as) (fromQ bs)
             GroupWith f as -> groupWith (fromQ . f . toQ) (fromQ as)
             SortWith f as -> sortWith (fromQ . f . toQ) (fromQ as)
             The as -> the (fromQ as)
             Last as -> last (fromQ as)
             Init as -> init (fromQ as)
             Index as i -> (fromQ as) !! (fromQ i)
             Reverse as -> reverse (fromQ as)
             Sum as -> sum (fromQ as)
             Product as -> product (fromQ as)
             Maximum as -> maximum (fromQ as)
             Minimum as -> minimum (fromQ as)
             Concat ass -> concat (fromQ ass)
             ConcatMap f as -> concatMap (fromQ . f . toQ) (fromQ as)
             Replicate i a -> replicate (fromQ i) (fromQ a)
             TakeWhile f as -> takeWhile (fromQ . f . toQ) (fromQ as)
             DropWhile f as -> dropWhile (fromQ . f . toQ) (fromQ as)
             ZipWith f as bs -> zipWith (\a b -> fromQ $ f (toQ a) (toQ b)) (fromQ as) (fromQ bs)


instance (QA a,QA b) => QA (a,b) where
  fromQ q = case q of
             ToQ a -> a
             Head as -> head (fromQ as)
             The as -> the (fromQ as)
             Last as -> last (fromQ as)
             Unzip as -> unzip (fromQ as)
             Index as i -> (fromQ as) !! (fromQ i)
             Sum as -> sum (fromQ as)
             Product as -> product (fromQ as)
             Maximum as -> maximum (fromQ as)
             Minimum as -> minimum (fromQ as)
             SplitAt i as -> splitAt (fromQ i) (fromQ as)
             Span f as -> span (fromQ . f . toQ) (fromQ as)
             Break f as -> break (fromQ . f . toQ) (fromQ as)


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

This module offers most of the functions on lists for the 'Q' type. Missing
functions are:

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
