{-# LANGUAGE GADTs, FlexibleInstances #-}

module Ferry
  (
    Q
  , QA
  , toQ
  , fromQ

  , nilQ
  , consQ
  , headQ
  , tailQ
  , takeQ
  , dropQ
  , mapQ
  , appendQ
  , filterQ
  , zipQ
  , unzipQ
  , groupWithQ
  , sortWithQ
  , theQ
  , lastQ
  , initQ
  , nullQ
  , lengthQ
  , indexQ
  , reverseQ
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
  Zip       :: (QA a, QA b) => Q [a] -> Q [b] -> Q [(a,b)]
  Unzip     :: (QA a, QA b) => Q [(a,b)] -> Q ([a],[b])
  GroupWith :: (Ord b, QA a, QA b) => (Q a -> Q b) -> Q [a] -> Q [[a]]
  SortWith  :: (Ord b, QA a, QA b) => (Q a -> Q b) -> Q [a] -> Q [a]



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

appendQ :: (QA a) => Q [a] -> Q [a] -> Q [a]
appendQ = Append

filterQ :: (QA a) => (Q a -> Q Bool) -> Q [a] -> Q [a]
filterQ = Filter

zipQ :: (QA a, QA b) => Q [a] -> Q [b] -> Q [(a,b)]
zipQ = Zip

unzipQ :: (QA a, QA b) => Q [(a,b)] -> Q ([a],[b])
unzipQ = Unzip

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

indexQ :: (QA a) => Q [a] -> Q Int -> Q a
indexQ = Index

reverseQ :: (QA a) => Q [a] -> Q [a]
reverseQ = Reverse

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


instance QA Char where
  fromQ q = case q of
             ToQ a -> a
             Head as -> head (fromQ as)
             The as -> the (fromQ as)
             Last as -> last (fromQ as)
             Index as i -> (fromQ as) !! (fromQ i)

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


instance (QA a,QA b) => QA (a,b) where
  fromQ q = case q of
             ToQ a -> a
             Head as -> head (fromQ as)
             The as -> the (fromQ as)
             Last as -> last (fromQ as)
             Unzip as -> unzip (fromQ as)
             Index as i -> (fromQ as) !! (fromQ i)

instance Show (Q a) where

instance Eq (Q Int) where

instance Num (Q Int) where
  (+) e1 e2 = Add e1 e2
  (*) e1 e2 = Mul e1 e2
  abs e1 = Abs e1
  negate e1 = Neg e1
  fromInteger i = ToQ (fromIntegral i)
  signum = Sgn