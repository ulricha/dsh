{-# LANGUAGE ScopedTypeVariables, FlexibleInstances, FlexibleContexts #-}

module Database.DSH.Combinators where

import Database.DSH.Data
import Prelude (Functor, fmap, Eq, Ord, Num, Bool(..), Integer, Double, Maybe, Either, undefined, ($), (.))

import Unsafe.Coerce (unsafeCoerce)

-- * Unit

unit :: Q S ()
unit = Q (UnitE $ reify (undefined :: ()))

-- * Boolean logic

false :: Q S Bool
false = Q (BoolE False BoolT)

true :: Q S Bool
true = Q (BoolE True BoolT)

not :: Q S Bool -> Q S Bool
not (Q b) = Q (AppE1 Not b $ reify (undefined :: Bool))

(&&) :: Q S Bool -> Q S Bool -> Q S Bool
(&&) (Q a) (Q b) = Q (AppE2 Conj a b $ reify (undefined :: Bool))

(||) :: Q S Bool -> Q S Bool -> Q S Bool
(||) (Q a) (Q b) = Q (AppE2 Disj a b $ reify (undefined :: Bool))

-- * Equality and Ordering

eq :: (Eq a, QA a (Q tb b)) => Q tb b -> Q tb b -> Q S Bool
eq (Q a) (Q b) = Q (AppE2 Equ a b $ reify (undefined :: Bool))

(==) :: (Eq a, QA a (Q tb b)) => Q tb b -> Q tb b -> Q S Bool
(==) = eq

neq :: (Eq a, QA a (Q tb b)) => Q tb b -> Q tb b -> Q S Bool
neq a b = not (eq a b)

(/=) :: (Eq a, QA a (Q tb b)) => Q tb b -> Q tb b -> Q S Bool
(/=) = neq

lt :: (Eq a, QA a (Q tb b)) => Q tb b -> Q tb b -> Q S Bool
lt (Q a) (Q b) = Q (AppE2 Lt a b $ reify (undefined :: Bool))

(<) :: (Eq a, QA a (Q tb b)) => Q tb b -> Q tb b -> Q S Bool
(<) = lt

lte :: (Eq a, QA a (Q tb b)) => Q tb b -> Q tb b -> Q S Bool
lte (Q a) (Q b) = Q (AppE2 Lte a b $ reify (undefined :: Bool))

(<=) :: (Eq a, QA a (Q tb b)) => Q tb b -> Q tb b -> Q S Bool
(<=) = lte

gte :: (Eq a, QA a (Q tb b)) => Q tb b -> Q tb b -> Q S Bool
gte (Q a) (Q b) = Q (AppE2 Gte a b $ reify (undefined :: Bool))

(>=) :: (Eq a, QA a (Q tb b)) => Q tb b -> Q tb b -> Q S Bool
(>=) = gte

gt :: (Eq a, QA a (Q tb b)) => Q tb b -> Q tb b -> Q S Bool
gt (Q a) (Q b) = Q (AppE2 Gt a b $ reify (undefined :: Bool))

(>) :: (Eq a, QA a (Q tb b)) => Q tb b -> Q tb b -> Q S Bool
(>) = gt

min :: forall a b tb. (Ord a, QA a (Q tb b)) => Q tb b -> Q tb b -> Q tb b
min (Q a) (Q b) = Q (AppE2 Min a b $ reify (undefined :: a))

max :: forall a b tb. (Ord a, QA a (Q tb b)) => Q tb b -> Q tb b -> Q tb b
max (Q a) (Q b) = Q (AppE2 Max a b $ reify (undefined :: a))


-- * Conditionals
-- | Boolean fold
-- | It's first argument is used in the case of False
-- | It's second argument is used in the case of True
-- | The third argument is the boolean
bool :: (QA a (Q tb b)) => Q tb b -> Q tb b -> Q S Bool -> Q tb b
bool f t b = cond b t f

cond :: forall a b tb. (QA a (Q tb b)) => Q S Bool -> Q tb b -> Q tb b -> Q tb b
cond (Q c) (Q a) (Q b) = Q (AppE3 Cond c a b $ reify (undefined :: a))

(?) :: (QA a (Q tb b)) => Q S Bool -> (Q tb b,Q tb b) -> Q tb b
(?) c (a,b) = cond c a b

-- * Maybe

listToMaybe :: QA a (Q tb b) => Q L (Q tb b) -> Q S (Maybe (Q tb b))
listToMaybe (Q as) = (Q as) 

maybeToList :: QA a (Q tb b) => Q S (Maybe (Q tb b)) -> Q L (Q tb b)
maybeToList (Q ma) = (Q ma)

nothing :: QA a (Q tb b) => Q S (Maybe (Q tb b))
nothing = listToMaybe nil

just :: QA a (Q tb b) => Q tb b -> Q S (Maybe (Q tb b))
just a = listToMaybe (singleton a)

isNothing :: QA a (Q tb b) => Q S (Maybe (Q tb b)) -> Q S Bool
isNothing ma = null (maybeToList ma)

isJust :: QA a (Q tb b) => Q S (Maybe (Q tb b)) -> Q S Bool
isJust ma = not (isNothing ma)

fromJust :: QA a (Q tb b) => Q S (Maybe (Q tb b)) -> Q tb b
fromJust ma = head (maybeToList ma)

maybe :: (QA a1 (Q ta a), QA b1 (Q tb b)) => Q tb b -> (Q ta a -> Q tb b) -> Q S (Maybe (Q ta a)) -> Q tb b
maybe b f ma = (isNothing ma) ? (b, f (fromJust (ma)))

fromMaybe :: QA a (Q tb b) => Q tb b -> Q S (Maybe (Q tb b)) -> Q tb b
fromMaybe a ma = (isNothing ma) ? (a, fromJust (ma))

catMaybes :: QA a (Q tb b) => Q L (Q S (Maybe (Q tb b))) -> Q L (Q tb b)
catMaybes mas = concatMap maybeToList mas

mapMaybe :: (QA a1 (Q ta a), QA b1 (Q tb b)) => (Q ta a -> Q S (Maybe (Q tb b))) -> Q L (Q ta a) -> Q L (Q tb b)
mapMaybe f as = concatMap (maybeToList . f) as

-- * Either

left :: (QA a1 (Q ta a),QA b1 (Q tb b)) => Q ta a -> Q S (Either (Q ta a) (Q tb b))
left a = tupleToEither (tuple ((singleton a),nil))

right :: (QA a1 (Q ta a),QA b1 (Q tb b)) => Q tb b -> Q S (Either (Q ta a) (Q tb b))
right a = tupleToEither (tuple (nil,(singleton a)))

isLeft :: (QA a1 (Q ta a),QA b1 (Q tb b)) => Q S (Either (Q ta a) (Q tb b)) -> Q S Bool
isLeft = null . snd . eitherToTuple

isRight :: (QA a1 (Q ta a),QA b1 (Q tb b)) => Q S (Either (Q ta a) (Q tb b)) -> Q S Bool
isRight = null . fst . eitherToTuple

either :: (QA a1 (Q ta a),QA b1 (Q tb b), QA c1 (Q tc c)) =>
          (Q ta a -> Q tc c) -> (Q tb b -> Q tc c) -> Q S (Either (Q ta a) (Q tb b)) -> Q tc c
either lf rf e = (isLeft e) ? ((lf . head . fst . eitherToTuple) e,(rf . head . snd . eitherToTuple) e)

lefts :: (QA a1 (Q ta a),QA b1 (Q tb b)) => Q L (Q S (Either (Q ta a) (Q tb b))) -> Q L (Q ta a)
lefts = concatMap (fst . eitherToTuple)

rights :: (QA a1 (Q ta a),QA b1 (Q tb b)) => Q L (Q S (Either (Q ta a) (Q tb b))) -> Q L (Q tb b)
rights = concatMap (snd . eitherToTuple)

partitionEithers :: (QA a1 (Q ta a),QA b1 (Q tb b)) => Q L (Q S (Either (Q ta a) (Q tb b))) -> Q S (Q L (Q ta a), Q L (Q tb b))
partitionEithers es = tuple (lefts es,rights es)

-- * List Construction

nil :: forall a b tb. (QA a (Q tb b)) => Q L (Q tb b)
nil = Q (ListE [] $ reify (undefined :: [a]))

empty :: forall a b tb. (QA a (Q tb b)) => Q L (Q tb b)
empty = nil

cons :: forall a b tb. (QA a (Q tb b)) => Q tb b -> Q L (Q tb b) -> Q L (Q tb b)
cons (Q a) (Q as) = Q (AppE2 Cons a as $ reify (undefined :: [a]))

(<|) :: forall a b tb. (QA a (Q tb b)) => Q tb b -> Q L (Q tb b) -> Q L (Q tb b)
(<|) = cons

snoc :: forall a b tb. (QA a (Q tb b)) => Q L (Q tb b) -> Q tb b -> Q L (Q tb b)
snoc (Q as) (Q a) = Q (AppE2 Snoc as a $ reify (undefined :: [a]))

(|>) :: forall a b tb. (QA a (Q tb b)) => Q L (Q tb b) -> Q tb b -> Q L (Q tb b)
(|>) = snoc

singleton :: (QA a (Q tb b)) => Q tb b -> Q L (Q tb b)
singleton a = cons a nil

-- * List Operations

head :: forall a b tb. (QA a (Q tb b)) => Q L (Q tb b) -> Q tb b
head (Q as) = Q (AppE1 Head as $ reify (undefined :: a))

tail :: forall a b tb. (QA a (Q tb b)) => Q L (Q tb b) -> Q L (Q tb b)
tail (Q as) = Q (AppE1 Tail as $ reify (undefined :: [a]))

take :: forall a b tb. (QA a (Q tb b)) => Q S Integer -> Q L (Q tb b) -> Q L (Q tb b)
take (Q i) (Q as) = Q (AppE2 Take i as $ reify (undefined :: [a]))

drop :: forall a b tb. (QA a (Q tb b)) => Q S Integer -> Q L (Q tb b) -> Q L (Q tb b)
drop (Q i) (Q as) = Q (AppE2 Drop i as $ reify (undefined :: [a]))

-- map :: forall a1 b1 a b ta tb. (QA a1 (Q ta a), QA b1 (Q tb b)) => (Q ta a -> Q tb b) ->  Q L (Q ta a) -> Q L (Q tb b)
-- map f (Q as) = Q (AppE2 Map (toLam1 f) as $ reify (undefined :: [b1]))

map :: (Q ta a -> Q tb b) -> Q L (Q ta a) -> Q L (Q tb b)
map f (Q as) = Q (AppE2 Map (toLam1 f) as undefined) -- $ reify (undefined :: [b1]))


append :: forall a b tb. (QA a (Q tb b)) => Q L (Q tb b) -> Q L (Q tb b) -> Q L (Q tb b)
append (Q as) (Q bs) = Q (AppE2 Append as bs $ reify (undefined :: [a]))

(><) :: (QA a (Q tb b)) => Q L (Q tb b) -> Q L (Q tb b) -> Q L (Q tb b)
(><) = append

filter :: forall a b tb. (QA a (Q tb b)) => (Q tb b -> Q S Bool) -> Q L (Q tb b) -> Q L (Q tb b)
filter f (Q as) = Q (AppE2 Filter (toLam1 f) as $ reify (undefined :: [a]))

groupWith ::  forall a1 b1 a b ta tb. (Ord b, QA a1 (Q ta a), QA b1 (Q tb b)) =>
              (Q ta a -> Q tb b) -> Q L (Q ta a) -> Q L (Q L (Q tb b))
groupWith f (Q as) = Q (AppE2 GroupWith (toLam1 f) as $ reify (undefined :: [[a1]]))

sortWith ::  forall a1 b1 a b ta tb. (Ord b, QA a1 (Q ta a), QA b1 (Q tb b)) =>
             (Q ta a -> Q tb b) -> Q L (Q ta a) -> Q L (Q ta a)
sortWith f (Q as) = Q (AppE2 SortWith (toLam1 f) as $ reify (undefined :: [a1]))

the :: forall a b tb. (Eq a, QA a (Q tb b)) => Q L (Q tb b) -> Q tb b
the (Q as) = Q (AppE1 The as $ reify (undefined :: a))

last :: forall a b tb. (Eq a, QA a (Q tb b)) => Q L (Q tb b) -> Q tb b
last (Q as) = Q (AppE1 Last as $ reify (undefined :: a))

init :: forall a b tb. (QA a (Q tb b)) => Q L (Q tb b) -> Q L (Q tb b)
init (Q as) = Q (AppE1 Init as $ reify (undefined :: [a]))

null :: (QA a (Q tb b)) => Q L (Q tb b) -> Q S Bool
null (Q as) = Q (AppE1 Null as $ reify (undefined :: Bool))

length :: (QA a (Q tb b)) => Q L (Q tb b) -> Q S Integer
length (Q as) = Q (AppE1 Length as $ reify (undefined :: Integer))

index :: forall a b tb. (QA a (Q tb b)) => Q L (Q tb b) -> Q S Integer -> Q tb b
index (Q as) (Q i) = Q (AppE2 Index as i $ reify (undefined :: a))

(!!) :: (QA a (Q tb b)) => Q L (Q tb b) -> Q S Integer -> Q tb b
(!!) = index

reverse :: forall a b tb. (QA a (Q tb b)) => Q L (Q tb b) -> Q L (Q tb b)
reverse (Q as) = Q (AppE1 Reverse as $ reify (undefined :: [a]))


-- * Special folds

and       :: Q L (Q S Bool) -> Q S Bool
and (Q as) = Q (AppE1 And as $ reify (undefined :: Bool))

or        :: Q L (Q S Bool) -> Q S Bool
or (Q as) = Q (AppE1 Or as $ reify (undefined :: Bool))

any       :: (QA a (Q tb b)) => (Q tb b -> Q S Bool) -> Q L (Q tb b) -> Q S Bool
any f (Q as) = Q (AppE2 Any (toLam1 f) as $ reify (undefined :: Bool))

all       :: (QA a (Q tb b)) => (Q tb b -> Q S Bool) -> Q L (Q tb b) -> Q S Bool
all f (Q as) = Q (AppE2 All (toLam1 f) as $ reify (undefined :: Bool))

sum       :: forall a b tb. (QA a (Q tb b), Num a) => Q L (Q tb b) -> Q tb b
sum (Q as) = Q (AppE1 Sum as $ reify (undefined :: a))

concat    :: forall a b tb. (QA a (Q tb b)) => Q L (Q L (Q tb b)) -> Q L (Q tb b)
concat (Q as) = Q (AppE1 Concat as $ reify (undefined :: [a]))

concatMap :: (QA a1 (Q ta a), QA b1 (Q tb b)) => (Q ta a -> Q L (Q tb b)) -> Q L (Q ta a) -> Q L (Q tb b)
concatMap f as = concat (map f as)

maximum   :: forall a b tb. (QA a (Q tb b), Ord a) => Q L (Q tb b) -> Q tb b
maximum (Q as) = Q (AppE1 Maximum as $ reify (undefined :: a))

minimum   :: forall a b tb. (QA a (Q tb b), Ord a) => Q L (Q tb b) -> Q tb b
minimum (Q as) = Q (AppE1 Minimum as $ reify (undefined :: a))

-- * Sublists

splitAt   :: forall a b tb. (QA a (Q tb b)) => Q S Integer -> Q L (Q tb b) -> Q S (Q L (Q tb b), Q L (Q tb b))
splitAt (Q i) (Q as) = Q (AppE2 SplitAt i as $ reify (undefined :: ([a],[a])))

takeWhile :: forall a b tb. (QA a (Q tb b)) => (Q tb b -> Q S Bool) -> Q L (Q tb b) -> Q L (Q tb b)
takeWhile f (Q as) = Q (AppE2 TakeWhile (toLam1 f) as $ reify (undefined :: [a]))

dropWhile :: forall a b tb. (QA a (Q tb b)) => (Q tb b -> Q S Bool) -> Q L (Q tb b) -> Q L (Q tb b)
dropWhile f (Q as) = Q (AppE2 DropWhile (toLam1 f) as $ reify (undefined :: [a]))

span      :: forall a tb b. (QA a (Q tb b)) => (Q tb b -> Q S Bool) -> Q L (Q tb b) -> Q S (Q L (Q tb b),Q L (Q tb b))
span f (Q as) = Q (AppE2 Span (toLam1 f) as $ reify (undefined :: ([a],[a])))

break     :: forall a tb b. (QA a (Q tb b)) => (Q tb b -> Q S Bool) -> Q L (Q tb b) -> Q S (Q L (Q tb b),Q L (Q tb b))
break f (Q as) = Q (AppE2 Break (toLam1 f) as $ reify (undefined :: ([a],[a])))


-- * Searching Lists

elem :: (Eq a, QA a (Q tb b)) => Q tb b -> Q L (Q tb b) -> Q S Bool
elem a as = (null (filter (a ==) as)) ? (false,true)

notElem :: (Eq a, QA a (Q tb b)) => Q tb b -> Q L (Q tb b) -> Q S Bool
notElem a as = not (elem a as)

-- lookup :: (QA a,QA b,Eq a) => Q a -> Q [(a, b)] -> Q (Maybe b)
-- lookup a  = listToMaybe . map snd . filter ((a ==) . fst)

-- * Zipping and Unzipping Lists

zip       :: forall a1 b1 a b ta tb. (QA a1 (Q ta a), QA b1 (Q tb b)) => Q L (Q ta a) -> Q L (Q tb b) -> Q L (Q ta a,Q tb b)
zip (Q as) (Q bs) = Q (AppE2 Zip as bs $ reify (undefined :: [(a1,b1)]))

zipWith   ::  forall a1 b1 c1 a b c ta tb tc. (QA a1 (Q ta a), QA b1 (Q tb b), QA c1 (Q tc c)) =>
              (Q ta a -> Q tb b -> Q tc c) -> Q L (Q ta a) -> Q L (Q tb b) -> Q L (Q tc c)
zipWith f (Q as) (Q bs) = Q (AppE3 ZipWith (toLam2 f) as bs $ reify (undefined :: [c1]))

unzip     ::  forall a1 b1 a b ta tb. (QA a1 (Q ta a), QA b1 (Q tb b)) =>
              Q L (Q ta a,Q tb b) -> Q S (Q L (Q ta a),Q L (Q tb b))
unzip (Q as) = Q (AppE1 Unzip as  $ reify (undefined :: ([a1],[b1])))

-- * "Set" operations

nub :: forall a b tb. (Eq a,QA a (Q tb b)) => Q L (Q tb b) -> Q L (Q tb b)
nub (Q as) = Q (AppE1 Nub as $ reify (undefined :: [a])) 


-- * Tuple Projection Functions

fst :: forall a1 b1 a b ta tb. (QA a1 (Q ta a), QA b1 (Q tb b)) => Q S (Q ta a,Q tb b) -> Q ta a
fst (Q a) = Q (AppE1 Fst a $ reify (undefined :: a1))

snd :: forall a1 b1 a b ta tb. (QA a1 (Q ta a), QA b1 (Q tb b)) => Q S (Q ta a,Q tb b) -> Q tb b
snd (Q a) = Q (AppE1 Snd a $ reify (undefined :: b1))


-- * Conversions between numeric types

integerToDouble :: Q S Integer -> Q S Double
integerToDouble (Q a) = Q (AppE1 IntegerToDouble a DoubleT)

infixl 9 !!
infixr 5 ><, <|, |>
infix  4  ==, /=, <, <=, >=, >
infixr 3  &&
infixr 2  ||
infix  0  ?

-- * Instances

instance Functor (Q L) where
  fmap = unsafeCoerce (map)


-- * Missing Combinators
-- $missing
-- 
-- {- $missing
-- 
-- This module offers most of the functions on lists given in PreludeList for the
-- 'Q' type. Missing functions are:
-- 
-- General folds:
-- 
-- > foldl
-- > foldl1
-- > scanl
-- > scanl1
-- > foldr
-- > foldr1
-- > scanr
-- > scanr1
-- 
-- Infinit lists:
-- 
-- > iterate
-- > repeat
-- > cycle
-- 
-- String functions:
-- 
-- > lines
-- > words
-- > unlines
-- > unwords
-- 
-- Zipping and unzipping lists:
-- 
-- > zip3
-- > zipWith3
-- > unzip3
-- 
-- -}
