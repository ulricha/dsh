{-# OPTIONS_GHC -fno-warn-orphans #-}

module Database.DSH.Combinators where

import Database.DSH.Data
-- import Database.DSH.TH

import Prelude (Eq, Ord, Num, Bool(..), Integer, Double, Maybe, Either, undefined, ($), (.))

-- * Unit

unit :: Exp ()
unit = UnitE 

-- * Boolean logic

false :: Exp Bool
false = BoolE False

true :: Exp Bool
true = BoolE True

not :: Exp Bool -> Exp Bool
not = AppE Not

(&&) :: Exp Bool -> Exp Bool -> Exp Bool
(&&) a b = AppE Conj (PairE a b)

(||) :: Exp Bool -> Exp Bool -> Exp Bool
(||) a b = AppE Disj (PairE a b)

-- * Equality and Ordering

eq :: (Reify (Exp a)) => Exp a -> Exp a -> Exp Bool
eq a b = AppE Equ (PairE a b)

(==) :: (Reify (Exp a)) => Exp a -> Exp a -> Exp Bool
(==) = eq

neq :: (Reify (Exp a)) => Exp a -> Exp a -> Exp Bool
neq a b = not (eq a b)

(/=) :: (Reify (Exp a)) => Exp a -> Exp a -> Exp Bool
(/=) = neq

lt :: (Reify (Exp a)) => Exp a -> Exp a -> Exp Bool
lt a b = AppE Lt (PairE a b)

(<) :: (Reify (Exp a)) => Exp a -> Exp a -> Exp Bool
(<) = lt

lte :: (Reify (Exp a)) => Exp a -> Exp a -> Exp Bool
lte a b = AppE Lte (PairE a b)

(<=) :: (Reify (Exp a)) => Exp a -> Exp a -> Exp Bool
(<=) = lte

gte :: (Reify (Exp a)) => Exp a -> Exp a -> Exp Bool
gte a b = AppE Gte (PairE a b)

(>=) :: (Reify (Exp a)) => Exp a -> Exp a -> Exp Bool
(>=) = gte

gt :: (Reify (Exp a)) => Exp a -> Exp a -> Exp Bool
gt a b = AppE Gt (PairE a b)

(>) :: (Reify (Exp a)) => Exp a -> Exp a -> Exp Bool
(>) = gt

min :: (Reify (Exp a)) => Exp a -> Exp a -> Exp a
min a b = AppE Min (PairE a b)

max :: (Reify (Exp a)) => Exp a -> Exp a -> Exp a
max a b = AppE Max (PairE a b)

-- * Conditionals

-- | Boolean fold
-- | It's first argument is used in the case of False
-- | It's second argument is used in the case of True
-- | The third argument is the boolean
bool :: (Reify (Exp a)) => Exp a -> Exp a -> Exp Bool -> Exp a
bool f t b = cond b t f

cond :: (Reify (Exp a)) => Exp Bool -> Exp a -> Exp a -> Exp a
cond c a b = AppE Cond (PairE c (PairE a b))

(?) :: (Reify (Exp a)) => Exp Bool -> (Exp a,Exp a) -> Exp a
(?) c (a,b) = cond c a b

-- {-
-- -- * Maybe
-- 
-- listToMaybe :: QA a => Q [a] -> Q (Maybe a)
-- listToMaybe (Q as) = (Q as) 
-- 
-- maybeToList :: QA a => Q (Maybe a) -> Q [a]
-- maybeToList (Q ma) = (Q ma)
-- 
-- nothing :: QA a => Q (Maybe a)
-- nothing = listToMaybe nil
-- 
-- just :: QA a => Q a -> Q (Maybe a)
-- just a = listToMaybe (singleton a)
-- 
-- isNothing :: QA a => Q (Maybe a) -> Q Bool
-- isNothing ma = null (maybeToList ma)
-- 
-- isJust :: QA a => Q (Maybe a) -> Q Bool
-- isJust ma = not (isNothing ma)
-- 
-- fromJust :: QA a => Q (Maybe a) -> Q a
-- fromJust ma = head (maybeToList ma)
-- 
-- maybe :: (QA a, QA b) => Q b -> (Q a -> Q b) -> Q (Maybe a) -> Q b
-- maybe b f ma = (isNothing ma) ? (b, f (fromJust (ma)))
-- 
-- fromMaybe :: QA a => Q a -> Q (Maybe a) -> Q a
-- fromMaybe a ma = (isNothing ma) ? (a, fromJust (ma))
-- 
-- catMaybes :: QA a => Q [Maybe a] -> Q [a]
-- catMaybes mas = concatMap maybeToList mas
-- 
-- mapMaybe :: (QA a, QA b) => (Q a -> Q (Maybe b)) -> Q [a] -> Q [b]
-- mapMaybe f as = concatMap (maybeToList . f) as
-- 
-- -- * Either
-- 
-- left :: (QA a,QA b) => Q a -> Q (Either a b)
-- left a = tupleToEither (tuple ((singleton a),nil))
-- 
-- right :: (QA a,QA b) => Q b -> Q (Either a b)
-- right a = tupleToEither (tuple (nil,(singleton a)))
-- 
-- isLeft :: (QA a,QA b) => Q (Either a b) -> Q Bool
-- isLeft = null . snd . eitherToTuple
-- 
-- isRight :: (QA a,QA b) => Q (Either a b) -> Q Bool
-- isRight = null . fst . eitherToTuple
-- 
-- either :: (QA a,QA b,QA c) => (Q a -> Q c) -> (Q b -> Q c) -> Q (Either a b) -> Q c
-- either lf rf e = (isLeft e) ? ((lf . head . fst . eitherToTuple) e,(rf . head . snd . eitherToTuple) e)
-- 
-- lefts :: (QA a,QA b) => Q [Either a b] -> Q [a]
-- lefts = concatMap (fst . eitherToTuple)
-- 
-- rights :: (QA a,QA b) => Q [Either a b] -> Q [b]
-- rights = concatMap (snd . eitherToTuple)
-- 
-- partitionEithers :: (QA a,QA b) => Q [Either a b] -> Q ([a], [b])
-- partitionEithers es = tuple (lefts es,rights es)
-- -}
-- * List Construction

nil :: (Reify (Exp a)) => Exp [Exp a]
nil = ListE []

empty :: (Reify (Exp a)) => Exp [Exp a]
empty = nil

cons :: (Reify (Exp a)) => Exp a -> Exp [Exp a] -> Exp [Exp a]
cons a as = AppE Cons (PairE a as)

(<|) :: (Reify (Exp a)) => Exp a -> Exp [Exp a] -> Exp [Exp a]
(<|) = cons

snoc :: (Reify (Exp a)) => Exp [Exp a] -> Exp a -> Exp [Exp a]
snoc as a = append as (singleton a)

(|>) :: (Reify (Exp a)) => Exp [Exp a] -> Exp a -> Exp [Exp a]
(|>) = snoc

singleton :: (Reify (Exp a)) => Exp a -> Exp [Exp a]
singleton a = cons a nil

-- * List Operations

head :: (Reify (Exp a)) => Exp [Exp a] -> Exp a
head = AppE Head

tail :: (Reify (Exp a)) => Exp [Exp a] -> Exp [Exp a]
tail = AppE Tail

take :: (Reify (Exp a)) => Exp Integer -> Exp [Exp a] -> Exp [Exp a]
take i as = AppE Take (PairE i as)

drop :: (Reify (Exp a)) => Exp Integer -> Exp [Exp a] -> Exp [Exp a]
drop i as = AppE Drop (PairE i as)

map :: (Reify (Exp a),Reify (Exp b)) => (Exp a -> Exp b) ->  Exp [Exp a] -> Exp [Exp b]
map f as = AppE Map (PairE (LamE f) as)

append :: (Reify (Exp a)) => Exp [Exp a] -> Exp [Exp a] -> Exp [Exp a]
append as bs = concat (ListE [as,bs])

(><) :: (Reify (Exp a)) => Exp [Exp a] -> Exp [Exp a] -> Exp [Exp a]
(><) = append

filter :: (Reify (Exp a)) => (Exp a -> Exp Bool) -> Exp [Exp a] -> Exp [Exp a]
filter f as = AppE Filter (PairE (LamE f) as)

groupWith :: (Reify (Exp a),Reify (Exp b)) => (Exp a -> Exp b) -> Exp [Exp a] -> Exp [Exp [Exp a]]
groupWith f as = AppE GroupWith (PairE (LamE f) as)

sortWith :: (Reify (Exp a),Reify (Exp b)) => (Exp a -> Exp b) -> Exp [Exp a] -> Exp [Exp a]
sortWith f as = AppE SortWith (PairE (LamE f) as)

the :: (Reify (Exp a)) => Exp [Exp a] -> Exp a
the = AppE The

last :: (Reify (Exp a)) => Exp [Exp a] -> Exp a
last = AppE Last

init :: (Reify (Exp a)) => Exp [Exp a] -> Exp [Exp a]
init = AppE Init

null :: (Reify (Exp a)) => Exp [Exp a] -> Exp Bool
null = AppE Null

length :: (Reify (Exp a)) => Exp [Exp a] -> Exp Integer
length = AppE Length

index :: (Reify (Exp a)) => Exp [Exp a] -> Exp Integer -> Exp a
index as i = AppE Index (PairE as i)

(!!) :: (Reify (Exp a)) => Exp [Exp a] -> Exp Integer -> Exp a
(!!) = index

reverse :: (Reify (Exp a)) => Exp [Exp a] -> Exp [Exp a]
reverse = AppE Reverse


-- * Special folds

and :: Exp ([Exp Bool]) -> Exp Bool
and = AppE And

or :: Exp ([Exp Bool]) -> Exp Bool
or = AppE Or

any :: (Reify (Exp a))  => (Exp a -> Exp Bool) -> Exp [Exp a] -> Exp Bool
any f = or . map f

all :: (Reify (Exp a))  => (Exp a -> Exp Bool) -> Exp [Exp a] -> Exp Bool
all f = and . map f

sum :: (Reify (Exp a)) => Exp [Exp a] -> Exp a
sum = AppE Sum

concat :: (Reify (Exp a)) => Exp [Exp [Exp a]] -> Exp [Exp a]
concat = AppE Concat

concatMap :: (Reify (Exp a),Reify (Exp b)) => (Exp a -> Exp [Exp b]) -> Exp [Exp a] -> Exp [Exp b]
concatMap f as = concat (map f as)

maximum :: (Reify (Exp a)) => Exp [Exp a] -> Exp a
maximum = AppE Maximum

minimum :: (Reify (Exp a)) => Exp [Exp a] -> Exp a
minimum = AppE Minimum

-- * Sublists

splitAt :: (Reify (Exp a)) => Exp Integer -> Exp [Exp a] -> Exp (Exp [Exp a], Exp [Exp a])
splitAt i as = AppE SplitAt (PairE i as)

takeWhile :: (Reify (Exp a)) => (Exp a -> Exp Bool) -> Exp [Exp a] -> Exp [Exp a]
takeWhile f as = AppE TakeWhile (PairE (LamE f) as)

dropWhile :: (Reify (Exp a)) => (Exp a -> Exp Bool) -> Exp [Exp a] -> Exp [Exp a]
dropWhile f as = AppE DropWhile (PairE (LamE f) as)

span :: (Reify (Exp a)) => (Exp a -> Exp Bool) -> Exp [Exp a] -> Exp (Exp [Exp a],Exp [Exp a])
span f as = pair (takeWhile f as) (dropWhile f as)

break :: (Reify (Exp a)) => (Exp a -> Exp Bool) -> Exp [Exp a] -> Exp (Exp [Exp a],Exp [Exp a])
break f as = span (not . f) as

-- * Searching Lists

elem :: (Reify (Exp a)) => Exp a -> Exp [Exp a] -> Exp Bool
elem a as = (null (filter (a ==) as)) ? (false,true)

notElem :: (Reify (Exp a)) => Exp a -> Exp [Exp a] -> Exp Bool
notElem a as = not (elem a as)

{-
lookup :: (QA a,QA b,Eq a) => Q a -> Q [(a, b)] -> Q (Maybe b)
lookup a  = listToMaybe . map snd . filter ((a ==) . fst)
-}

-- * Zipping and Unzipping Lists

zip :: (Reify (Exp a),Reify (Exp b)) => Exp [Exp a] -> Exp [Exp b] -> Exp [Exp (Exp a,Exp b)]
zip as bs = AppE Zip (PairE as bs)

zipWith   :: (Reify (Exp a),Reify (Exp b),Reify (Exp c)) => (Exp a -> Exp b -> Exp c) -> Exp [Exp a] -> Exp [Exp b] -> Exp [Exp c]
zipWith f as bs = map (\e -> f (fst e) (snd e)) (zip as bs)

unzip :: (Reify (Exp a),Reify (Exp b)) => Exp [Exp (Exp a,Exp b)] -> Exp (Exp [Exp a], Exp [Exp b])
unzip = AppE Unzip

-- * "Set" operations

nub :: (Reify (Exp a)) => Exp [Exp a] -> Exp [Exp a]
nub = AppE Nub

-- * Tuple Projection Functions

fst :: (Reify (Exp a),Reify (Exp b)) => Exp (Exp a,Exp b) -> Exp a
fst = AppE Fst

snd :: (Reify (Exp a),Reify (Exp b)) => Exp (Exp a,Exp b) -> Exp b
snd = AppE Snd

pair :: (Reify (Exp a),Reify (Exp b)) => Exp a -> Exp b -> Exp (Exp a,Exp b)
pair = PairE

-- * Conversions between numeric types

integerToDouble :: Exp Integer -> Exp Double
integerToDouble = AppE IntegerToDouble

-- * Rebind Monadic Combinators

return :: (Reify (Exp a)) => Exp a -> Exp [Exp a]
return = singleton

(>>=) :: (Reify (Exp a),Reify (Exp b)) => Exp [Exp a] -> (Exp a -> Exp [Exp b]) -> Exp [Exp b]
(>>=) ma f = concatMap f ma

(>>) :: (Reify (Exp a),Reify (Exp b)) => Exp [Exp a] -> Exp [Exp b] -> Exp [Exp b]
(>>) ma mb = concatMap (\_ -> mb) ma

mzip :: (Reify (Exp a),Reify (Exp b)) => Exp [Exp a] -> Exp [Exp b] -> Exp [Exp (Exp a,Exp b)]
mzip = zip

guard :: Exp Bool -> Exp [Exp ()]
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
