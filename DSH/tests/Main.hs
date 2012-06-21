{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# LANGUAGE ViewPatterns #-}

module Main where

import qualified Database.DSH as Q
import Database.DSH (Q, QA)

#if !defined(isDBPH) & !defined(isX100)
#define isFerry
#endif

-- import Database.DSH.Interpreter (fromQ)
#ifdef isDBPH 
import Database.DSH.Flattening (fromQ)
#elif isX100
import Database.DSH.Flattening (fromX100)
#define isDBPH 
#else
import Database.DSH.Compiler (fromQ)
#endif

#ifdef isX100
import Database.X100Client
#endif

#ifndef isX100
import qualified Database.HDBC as HDBC
import Database.HDBC.PostgreSQL
#endif


import System.Environment
import Test.Framework (Test, defaultMainWithArgs, testGroup)
import Test.Framework.Providers.QuickCheck2 (testProperty)
import Test.QuickCheck
import Test.QuickCheck.Monadic

import Data.List
import Data.Maybe
import Data.Either
import GHC.Exts

import Data.Text (Text)
import qualified Data.Text as Text

import Data.Char

instance Arbitrary Text where
  arbitrary = fmap Text.pack arbitrary

#ifdef isX100
getConn :: IO X100Info
getConn = return $ x100Info "localhost" "48130" Nothing    
#else
getConn :: IO Connection
getConn = connectPostgreSQL "user = 'postgres' password = 'haskell98' host = 'localhost' port = '5432' dbname = 'ferry'"
#endif

main :: IO ()
main = do
            args <- getArgs
            let args' = if or $ map (isPrefixOf "-s") args
                         then args
                         else "-s5":args
            defaultMainWithArgs tests args'

tests :: [Test]
tests = 
    [
      testGroup "Supported Types"
        [ testProperty "()" $ prop_unit
        , testProperty "()" $ prop_unit
        , testProperty "Bool" $ prop_bool
        , testProperty "Char" $ prop_char
        , testProperty "Text" $ prop_text
        , testProperty "Integer" $ prop_integer
        , testProperty "Double" $ prop_double
        , testProperty "[Integer]" $ prop_list_integer_1
        , testProperty "[[Integer]]" $ prop_list_integer_2
        , testProperty "[[[Integer]]]" $ prop_list_integer_3
        , testProperty "[(Integer, Integer)]" $ prop_list_tuple_integer
        , testProperty "([], [])" $ prop_tuple_list_integer
        , testProperty "Maybe Integer" $ prop_maybe_integer
        , testProperty "Either Integer Integer" $ prop_either_integer
        ]
    , testGroup "Equality, Boolean Logic and Ordering"
        [ testProperty "&&" $ prop_infix_and
        , testProperty "||" $ prop_infix_or
        , testProperty "not" $ prop_not
        , testProperty "eq" $ prop_eq
        , testProperty "neq" $ prop_neq
        , testProperty "cond" $ prop_cond
        , testProperty "cond tuples" $ prop_cond_tuples
        , testProperty "cond ([[Integer]], [[Integer]])" $ prop_cond_list_tuples
        , testProperty "lt" $ prop_lt
        , testProperty "lte" $ prop_lte
        , testProperty "gt" $ prop_gt
        , testProperty "gte" $ prop_gte
        , testProperty "min_integer" $ prop_min_integer
        , testProperty "min_double" $ prop_min_double
        , testProperty "max_integer" $ prop_max_integer
        , testProperty "max_double" $ prop_max_double
        ]
    , testGroup "Tuples"
        [ testProperty "fst" $ prop_fst
        , testProperty "snd" $ prop_snd
        ]
    , testGroup "Numerics"
        [ testProperty "add_integer" $ prop_add_integer
        , testProperty "add_double" $ prop_add_double
        , testProperty "mul_integer" $ prop_mul_integer
        , testProperty "mul_double" $ prop_mul_double
        , testProperty "div_double" $ prop_div_double
        , testProperty "integer_to_double" $ prop_integer_to_double    
        , testProperty "abs_integer" $ prop_abs_integer
        , testProperty "abs_double" $ prop_abs_double
        , testProperty "signum_integer" $ prop_signum_integer
        , testProperty "signum_double" $ prop_signum_double
        , testProperty "negate_integer" $ prop_negate_integer
        , testProperty "negate_double" $ prop_negate_double
        ]
    , testGroup "Lists"
        [ testProperty "head" $ prop_head
        , testProperty "tail" $ prop_tail
        , testProperty "cons" $ prop_cons
        , testProperty "snoc" $ prop_snoc
        , testProperty "take" $ prop_take
#ifndef isDBPH        
        , testProperty "drop" $ prop_drop
#endif
        , testProperty "take ++ drop" $ prop_takedrop
        , testProperty "map" $ prop_map
        , testProperty "filter" $ prop_filter
        , testProperty "the" $ prop_the
#ifdef isX100  
        , testProperty "last" $ prop_last
#endif
        , testProperty "init" $ prop_init
        , testProperty "null" $ prop_null
        , testProperty "length" $ prop_length
        , testProperty "length tuple list" $ prop_length_tuple
        , testProperty "index" $ prop_index
#ifdef isX100        
        , testProperty "index [[]]" $ prop_index_nest
#endif
        , testProperty "reverse" $ prop_reverse
        , testProperty "reverse [[]]" $ prop_reverse_nest
        , testProperty "append" $ prop_append
        , testProperty "append nest" $ prop_append_nest
        , testProperty "groupWith" $ prop_groupWith
#ifdef isX100
        , testProperty "groupWith length" $ prop_groupWith_length
#endif
        , testProperty "sortWith" $ prop_sortWith
        , testProperty "and" $ prop_and
        , testProperty "or" $ prop_or
        , testProperty "any_zero" $ prop_any_zero
        , testProperty "all_zero" $ prop_all_zero
        , testProperty "sum_integer" $ prop_sum_integer
        , testProperty "sum_double" $ prop_sum_double
        , testProperty "concat" $ prop_concat
        , testProperty "concatMap" $ prop_concatMap
        , testProperty "maximum" $ prop_maximum
        , testProperty "minimum" $ prop_minimum
        , testProperty "splitAt" $ prop_splitAt
        , testProperty "takeWhile" $ prop_takeWhile
        , testProperty "dropWhile" $ prop_dropWhile
#ifndef isDBPH
        , testProperty "dropWhile" $ prop_dropWhile
        , testProperty "span" $ prop_span
        , testProperty "break" $ prop_break
#endif
        , testProperty "elem" $ prop_elem
        , testProperty "notElem" $ prop_notElem
        , testProperty "zip" $ prop_zip
#ifndef isDBPH
        , testProperty "zipWith" $ prop_zipWith
#endif
        , testProperty "unzip" $ prop_unzip
        , testProperty "nub" $ prop_nub
        ]
    , testGroup "Lifted operations"
        [ testProperty "Lifted &&" $ prop_infix_map_and
        , testProperty "Lifted ||" $ prop_infix_map_or
        , testProperty "Lifted not" $ prop_map_not
        , testProperty "Lifted eq" $ prop_map_eq
        , testProperty "Lifted neq" $ prop_map_neq
        , testProperty "Lifted cond" $ prop_map_cond
        , testProperty "Lifted cond tuples" $ prop_map_cond_tuples
#ifndef isFerry        
        , testProperty "Lifted cond + concat" $ prop_concatmapcond
#endif
        , testProperty "Lifted lt" $ prop_map_lt
        , testProperty "Lifted lte" $ prop_map_lte
        , testProperty "Lifted gt" $ prop_map_gt
        , testProperty "Lifted gte" $ prop_map_gte
        , testProperty "Lifted cons" $ prop_map_cons
        , testProperty "Lifted concat" $ prop_map_concat
        , testProperty "Lifted fst" $ prop_map_fst
        , testProperty "Lifted snd" $ prop_map_snd
#ifdef isX100
        , testProperty "Lifted the" $ prop_map_the
#endif
        --, testProperty "Lifed and" $ prop_map_and
        , testProperty "map (map (*2))" $ prop_map_map_mul
        , testProperty "map (map (map (*2)))" $ prop_map_map_map_mul
        , testProperty "map (\\x -> map (\\y -> x + y) ..) .." $ prop_map_map_add
        , testProperty "Lifted groupWith" $ prop_map_groupWith
        , testProperty "Lifted sortWith" $ prop_map_sortWith
        , testProperty "Lifted sortWith length" $ prop_map_sortWith_length
#ifdef isX100        
        , testProperty "Lifted groupWith length" $ prop_map_groupWith_length
#endif        
        , testProperty "Lifted length" $ prop_map_length
        , testProperty "Lifted length on [[(a,b)]]" $ prop_map_length_tuple
        , testProperty "Sortwith length nested" $ prop_sortWith_length_nest
#ifdef isX100
        , testProperty "GroupWith length nested" $ prop_groupWith_length_nest
#endif
        , testProperty "Lift minimum" $ prop_map_minimum
        , testProperty "map (map minimum)" $ prop_map_map_minimum
        , testProperty "Lift maximum" $ prop_map_maximum
        , testProperty "map (map maximum)" $ prop_map_map_maximum
        , testProperty "map integer_to_double" $ prop_map_integer_to_double
#ifdef isX100
        , testProperty "map tail" $ prop_map_tail    
#endif        
        , testProperty "map unzip" $ prop_map_unzip
        , testProperty "map reverse" $ prop_map_reverse
        , testProperty "map reverse [[]]" $ prop_map_reverse_nest
        , testProperty "map and" $ prop_map_and
        , testProperty "map (map and)" $ prop_map_map_and
        , testProperty "map sum" $ prop_map_sum
        , testProperty "map (map sum)" $ prop_map_map_sum
        , testProperty "map or" $ prop_map_or
        , testProperty "map (map or)" $ prop_map_map_or
        , testProperty "map any zero" $ prop_map_any_zero
        , testProperty "map all zero" $ prop_map_all_zero
        , testProperty "map filter" $ prop_map_filter
        , testProperty "map append" $ prop_map_append
        , testProperty "map index" $ prop_map_index
        , testProperty "map index [[]]" $ prop_map_index_nest
        , testProperty "map init" $ prop_map_init
        , testProperty "map last" $ prop_map_last
        , testProperty "map null" $ prop_map_null
        , testProperty "map nub" $ prop_map_nub
        , testProperty "map snoc" $ prop_map_snoc
        , testProperty "map take" $ prop_map_take
        , testProperty "map drop" $ prop_map_drop
        , testProperty "map zip" $ prop_map_zip
        , testProperty "map takeWhile" $ prop_map_takeWhile
        , testProperty "map dropWhile" $ prop_map_dropWhile
        ]
    ]

makeProp :: (Eq b, QA a, QA b, Show a, Show b)
            => (Q a -> Q b)
            -> (a -> b)
            -> a
            -> Property
makeProp f1 f2 arg = monadicIO $ do
#ifdef isX100
    c  <- run $ getConn
    db <- run $ fromX100 c $ f1 (Q.toQ arg)
#else
    c  <- run $ getConn
    db <- run $ fromQ c $ f1 (Q.toQ arg)
    run $ HDBC.disconnect c
#endif
    let hs = f2 arg
    assert (db == hs)

makePropNotNull ::  (Eq b, Q.QA a, Q.QA b, Show a, Show b)
                    => (Q.Q [a] -> Q.Q b)
                    -> ([a] -> b)
                    -> [a]
                    -> Property
makePropNotNull q f arg = not (null arg) ==> makeProp q f arg

makePropDouble :: (QA a, Show a)
                  => (Q a -> Q Double)
                  -> (a -> Double)
                  -> a
                  -> Property
makePropDouble f1 f2 arg = monadicIO $ do
#ifdef isX100
    c  <- run $ getConn
    db <- run $ fromX100 c $ f1 (Q.toQ arg)
#else
    c  <- run $ getConn
    db <- run $ fromQ c $ f1 (Q.toQ arg)
    run $ HDBC.disconnect c
#endif
    let hs = f2 arg
    let eps = 1.0E-8 :: Double;    
    assert (abs (db - hs) < eps)

makePropListDouble :: (QA a, Show a)
                  => (Q a -> Q [Double])
                  -> (a -> [Double])
                  -> a
                  -> Property
makePropListDouble f1 f2 arg = monadicIO $ do
#ifdef isX100
    c  <- run $ getConn
    db <- run $ fromX100 c $ f1 (Q.toQ arg)
#else
    c  <- run $ getConn
    db <- run $ fromQ c $ f1 (Q.toQ arg)
    run $ HDBC.disconnect c
#endif
    let hs = f2 arg
    let eps = 1.0E-8 :: Double;    
    assert $ and [abs (d - h) < eps | (d, h) <- zip db hs]

uncurryQ :: (Q.QA a, Q.QA b) => (Q.Q a -> Q.Q b -> Q.Q c) -> Q.Q (a,b) -> Q.Q c
uncurryQ f = uncurry f . Q.view

-- * Supported Types

prop_unit :: () -> Property
prop_unit = makeProp id id

prop_bool :: Bool -> Property
prop_bool = makeProp id id

prop_integer :: Integer -> Property
prop_integer = makeProp id id

prop_double :: Double -> Property
prop_double = makePropDouble id id

prop_char :: Char -> Property
prop_char c = isPrint c ==> makeProp id id c

prop_text :: Text -> Property
prop_text t = Text.all isPrint t ==> makeProp id id t

prop_list_integer_1 :: [Integer] -> Property
prop_list_integer_1 = makeProp id id

prop_list_integer_2 :: [[Integer]] -> Property
prop_list_integer_2 = makeProp id id

prop_list_integer_3 :: [[[Integer]]] -> Property
prop_list_integer_3 = makeProp id id

prop_list_tuple_integer :: [(Integer, Integer)] -> Property
prop_list_tuple_integer = makeProp id id

prop_maybe_integer :: Maybe Integer -> Property
prop_maybe_integer = makeProp id id

prop_tuple_list_integer :: ([Integer], [Integer]) -> Property
prop_tuple_list_integer = makeProp id id

prop_either_integer :: Either Integer Integer -> Property
prop_either_integer = makeProp id id

-- * Equality, Boolean Logic and Ordering

prop_infix_and :: (Bool,Bool) -> Property
prop_infix_and = makeProp (uncurryQ (Q.&&)) (uncurry (&&))

prop_infix_map_and :: (Bool, [Bool]) -> Property
prop_infix_map_and = makeProp (\x -> Q.map ((Q.fst x) Q.&&) $ Q.snd x) (\(x,xs) -> map (x &&) xs)
                     
prop_infix_or :: (Bool,Bool) -> Property
prop_infix_or = makeProp (uncurryQ (Q.||)) (uncurry (||))

prop_infix_map_or :: (Bool, [Bool]) -> Property
prop_infix_map_or = makeProp (\x -> Q.map ((Q.fst x) Q.||) $ Q.snd x) (\(x,xs) -> map (x ||) xs)

prop_not :: Bool -> Property
prop_not = makeProp Q.not not

prop_map_not :: [Bool] -> Property
prop_map_not = makeProp (Q.map Q.not) (map not)

prop_eq :: (Integer,Integer) -> Property
prop_eq = makeProp (uncurryQ (Q.==)) (uncurry (==))

prop_map_eq :: (Integer, [Integer]) -> Property
prop_map_eq = makeProp (\x -> Q.map ((Q.fst x) Q.==) $ Q.snd x) (\(x,xs) -> map (x ==) xs)

prop_neq :: (Integer,Integer) -> Property
prop_neq = makeProp (uncurryQ (Q./=)) (uncurry (/=))

prop_map_neq :: (Integer, [Integer]) -> Property
prop_map_neq = makeProp (\x -> Q.map ((Q.fst x) Q./=) $ Q.snd x) (\(x,xs) -> map (x /=) xs)

prop_cond :: Bool -> Property
prop_cond = makeProp (\b -> Q.cond b (0 :: Q Integer) 1) (\b -> if b then 0 else 1)

prop_cond_tuples :: (Bool, (Integer, Integer)) -> Property
prop_cond_tuples = makeProp (\b -> Q.cond (Q.fst b) (Q.tuple ((Q.fst $ Q.snd b), (Q.fst $ Q.snd b))) (Q.tuple ((Q.snd $ Q.snd b), (Q.snd $ Q.snd b)))) (\b -> if fst b then (fst $ snd b, fst $ snd b) else (snd $ snd b, snd $ snd b))

prop_cond_list_tuples :: (Bool, ([[Integer]], [[Integer]])) -> Property
prop_cond_list_tuples = makeProp (\b -> Q.cond (Q.fst b) (Q.tuple ((Q.fst $ Q.snd b), (Q.fst $ Q.snd b))) (Q.tuple ((Q.snd $ Q.snd b), (Q.snd $ Q.snd b)))) (\b -> if fst b then (fst $ snd b, fst $ snd b) else (snd $ snd b, snd $ snd b))

prop_map_cond :: [Bool] -> Property
prop_map_cond = makeProp (Q.map (\b -> Q.cond b (0 :: Q Integer) 1)) (map (\b -> if b then 0 else 1))

prop_map_cond_tuples :: [Bool] -> Property
prop_map_cond_tuples = makeProp (Q.map (\b -> Q.cond b (Q.toQ (0, 10) :: Q (Integer, Integer)) (Q.toQ (1, 11)))) (map (\b -> if b then (0, 10) else (1, 11)))

prop_concatmapcond :: [Integer] -> Property
prop_concatmapcond l1 = 
        -- FIXME remove precondition as soon as X100 is fixed
	(not $ null l1)
	==>
	makeProp q n l1
        where q l = Q.concatMap (\x -> Q.cond ((Q.>) x (Q.toQ 0)) (x Q.<| el) el) l
              n l = concatMap (\x -> if x > 0 then [x] else []) l
              el = Q.toQ []

prop_lt :: (Integer, Integer) -> Property
prop_lt = makeProp (uncurryQ (Q.<)) (uncurry (<))

prop_map_lt :: (Integer, [Integer]) -> Property
prop_map_lt = makeProp (\x -> Q.map ((Q.fst x) Q.<) $ Q.snd x) (\(x,xs) -> map (x <) xs)

prop_lte :: (Integer, Integer) -> Property
prop_lte = makeProp (uncurryQ (Q.<=)) (uncurry (<=))

prop_map_lte :: (Integer, [Integer]) -> Property
prop_map_lte = makeProp (\x -> Q.map ((Q.fst x) Q.<=) $ Q.snd x) (\(x,xs) -> map (x <=) xs)

prop_gt :: (Integer, Integer) -> Property
prop_gt = makeProp (uncurryQ (Q.>)) (uncurry (>))

prop_map_gt :: (Integer, [Integer]) -> Property
prop_map_gt = makeProp (\x -> Q.map ((Q.fst x) Q.>) $ Q.snd x) (\(x,xs) -> map (x >) xs)

prop_gte :: (Integer, Integer) -> Property
prop_gte = makeProp (uncurryQ (Q.>=)) (uncurry (>=))

prop_map_gte :: (Integer, [Integer]) -> Property
prop_map_gte = makeProp (\x -> Q.map ((Q.fst x) Q.>=) $ Q.snd x) (\(x,xs) -> map (x >=) xs)

prop_min_integer :: (Integer,Integer) -> Property
prop_min_integer = makeProp (uncurryQ Q.min) (uncurry min)

prop_max_integer :: (Integer,Integer) -> Property
prop_max_integer = makeProp (uncurryQ Q.max) (uncurry max)

prop_min_double :: (Double,Double) -> Property
prop_min_double = makePropDouble (uncurryQ Q.min) (uncurry min)

prop_max_double :: (Double,Double) -> Property
prop_max_double = makePropDouble (uncurryQ Q.max) (uncurry max)

-- * Maybe

prop_maybe :: (Integer, Maybe Integer) -> Property
prop_maybe =  makeProp (\a -> Q.maybe (Q.fst a) id (Q.snd a)) (\(i,mi) -> maybe i id mi)

prop_just :: Integer -> Property
prop_just = makeProp Q.just Just

prop_isJust :: Maybe Integer -> Property
prop_isJust = makeProp Q.isJust isJust

prop_isNothing :: Maybe Integer -> Property
prop_isNothing = makeProp Q.isNothing isNothing

prop_fromJust :: Maybe Integer -> Property
prop_fromJust mi = isJust mi ==> makeProp Q.fromJust fromJust mi

prop_fromMaybe :: (Integer,Maybe Integer) -> Property
prop_fromMaybe = makeProp (uncurryQ Q.fromMaybe) (uncurry fromMaybe)

prop_listToMaybe :: [Integer] -> Property
prop_listToMaybe = makeProp Q.listToMaybe listToMaybe

prop_maybeToList :: Maybe Integer -> Property
prop_maybeToList = makeProp Q.maybeToList maybeToList

prop_catMaybes :: [Maybe Integer] -> Property
prop_catMaybes = makeProp Q.catMaybes catMaybes

prop_mapMaybe :: [Maybe Integer] -> Property
prop_mapMaybe = makeProp (Q.mapMaybe id) (mapMaybe id)

-- * Either

prop_left :: Integer -> Property
prop_left = makeProp (Q.left :: Q Integer -> Q (Either Integer Integer)) Left

prop_right :: Integer -> Property
prop_right = makeProp (Q.right :: Q Integer -> Q (Either Integer Integer)) Right

prop_isLeft :: Either Integer Integer -> Property
prop_isLeft = makeProp Q.isLeft (\e -> case e of {Left _ -> True; Right _ -> False;})

prop_isRight :: Either Integer Integer -> Property
prop_isRight = makeProp Q.isRight (\e -> case e of {Left _ -> False; Right _ -> True;})

prop_either :: (Either Integer Integer) -> Property
prop_either =  makeProp (Q.either id id) (either id id)

prop_lefts :: [Either Integer Integer] -> Property
prop_lefts =  makeProp Q.lefts lefts

prop_rights :: [Either Integer Integer] -> Property
prop_rights =  makeProp Q.rights rights

prop_partitionEithers :: [Either Integer Integer] -> Property
prop_partitionEithers =  makeProp Q.partitionEithers partitionEithers

-- * Lists

prop_cons :: (Integer, [Integer]) -> Property
prop_cons = makeProp (uncurryQ (Q.<|)) (uncurry (:))

prop_map_cons :: (Integer, [[Integer]]) -> Property
prop_map_cons = makeProp (\x -> Q.map ((Q.fst x) Q.<|) $ Q.snd x) (\(x,xs) -> map (x:) xs)

prop_snoc :: ([Integer], Integer) -> Property
prop_snoc = makeProp (uncurryQ (Q.|>)) (\(a,b) -> a ++ [b])

prop_map_snoc :: ([Integer], [Integer]) -> Property
prop_map_snoc = makeProp (\z -> Q.map ((Q.fst z) Q.|>) (Q.snd z)) (\(a,b) -> map (\z -> a ++ [z]) b)

prop_singleton :: Integer -> Property
prop_singleton = makeProp Q.singleton (\x -> [x])

prop_head  :: [Integer] -> Property
prop_head  = makePropNotNull Q.head head

prop_tail  :: [Integer] -> Property
prop_tail  = makePropNotNull Q.tail tail

prop_last  :: [Integer] -> Property
prop_last  = makePropNotNull Q.last last

prop_map_last :: [[Integer]] -> Property
prop_map_last ps = and (map ((>0) . length) ps) ==> makeProp (Q.map Q.last) (map last) ps

prop_init  :: [Integer] -> Property
prop_init  = makePropNotNull Q.init init

prop_map_init  :: [[Integer]] -> Property
prop_map_init  ps = and (map ((>0) . length) ps)
    ==>
     makeProp (Q.map Q.init) (map init) ps

prop_the   :: (Int, Integer) -> Property
prop_the (n, i) = 
  n > 0
  ==>
  let l = replicate n i in makeProp Q.the the l
                           
prop_map_the :: [(Int, Integer)] -> Property
prop_map_the ps =
  let ps' = filter ((>0) . fst) ps in
  (length ps') > 0
  ==>
  let xss = map (\(n, i) -> replicate n i) ps' in
  makeProp (Q.map Q.the) (map the) xss

prop_map_tail :: [[Integer]] -> Property
prop_map_tail ps =
    and [length p > 0 | p <- ps]
    ==>
    makeProp (Q.map Q.tail) (map tail) ps

prop_index :: ([Integer], Integer)  -> Property
prop_index (l, i) =
        i > 0 && i < fromIntegral (length l)
    ==> makeProp (uncurryQ (Q.!!))
                 (\(a,b) -> a !! fromIntegral b)
                 (l, i)

prop_index_nest :: ([[Integer]], Integer)  -> Property
prop_index_nest (l, i) =
     i > 0 && i < fromIntegral (length l)
 ==> makeProp (uncurryQ (Q.!!))
              (\(a,b) -> a !! fromIntegral b)
              (l, i)

prop_map_index :: ([Integer], [Integer])  -> Property
prop_map_index (l, is) =
     and [i >= 0 && i < 2 * fromIntegral (length l) | i <-  is]
 ==> makeProp (\z -> Q.map (((Q.fst z) Q.++ (Q.fst z) Q.++ (Q.fst z)) Q.!!) (Q.snd z))
              (\(a,b) -> map ((a ++ a ++ a) !!) (map fromIntegral b))
              (l, is)

prop_map_index_nest :: ([[Integer]], [Integer])  -> Property
prop_map_index_nest (l, is) =
   and [i >= 0 && i < 3 * fromIntegral (length l) | i <-  is]
 ==> makeProp (\z -> Q.map (((Q.fst z) Q.++ (Q.fst z) Q.++ (Q.fst z)) Q.!!) (Q.snd z))
            (\(a,b) -> map ((a ++ a ++ a) !!) (map fromIntegral b))
            (l, is)
            
prop_take :: (Integer, [Integer]) -> Property
prop_take = makeProp (uncurryQ Q.take) (\(n,l) -> take (fromIntegral n) l)

prop_map_take :: (Integer, [[Integer]]) -> Property
prop_map_take = makeProp (\z -> Q.map (Q.take $ Q.fst z) $ Q.snd z) (\(n,l) -> map (take (fromIntegral n)) l)

prop_drop :: (Integer, [Integer]) -> Property
prop_drop = makeProp (uncurryQ Q.drop) (\(n,l) -> drop (fromIntegral n) l)

prop_map_drop :: (Integer, [[Integer]]) -> Property
prop_map_drop = makeProp (\z -> Q.map (Q.drop $ Q.fst z) $ Q.snd z) (\(n,l) -> map (drop (fromIntegral n)) l)

prop_takedrop :: (Integer, [Integer]) -> Property
prop_takedrop = makeProp takedrop_q takedrop
  where takedrop_q = \p -> Q.append ((Q.take (Q.fst p)) (Q.snd p)) ((Q.drop (Q.fst p)) (Q.snd p))
        takedrop (n, l) = (take (fromIntegral n) l) ++ (drop (fromIntegral n) l)

prop_map :: [Integer] -> Property
prop_map = makeProp (Q.map id) (map id)

prop_map_map_mul :: [[Integer]] -> Property
prop_map_map_mul = makeProp (Q.map (Q.map (*2))) (map (map (*2)))

prop_map_map_add :: ([Integer], [Integer]) -> Property
prop_map_map_add = makeProp (\z -> Q.map (\x -> (Q.map (\y -> x + y) $ Q.snd z)) $ Q.fst z) (\(l,r) -> map (\x -> map (\y -> x + y) r) l)
                   
prop_map_map_map_mul :: [[[Integer]]] -> Property
prop_map_map_map_mul = makeProp (Q.map (Q.map (Q.map (*2)))) (map (map (map (*2))))

prop_append :: ([Integer], [Integer]) -> Property
prop_append = makeProp (uncurryQ (Q.><)) (\(a,b) -> a ++ b)

prop_append_nest :: ([[Integer]], [[Integer]]) -> Property
prop_append_nest = makeProp (uncurryQ (Q.><)) (\(a,b) -> a ++ b)

prop_map_append :: ([Integer], [[Integer]]) -> Property
prop_map_append = makeProp (\z -> Q.map (Q.fst z Q.++) (Q.snd z)) (\(a,b) -> map (a ++) b)

prop_filter :: [Integer] -> Property
prop_filter = makeProp (Q.filter (const $ Q.toQ True)) (filter $ const True)

prop_map_filter :: [[Integer]] -> Property
prop_map_filter = makeProp (Q.map (Q.filter (const $ Q.toQ True))) (map (filter $ const True))

prop_groupWith :: [Integer] -> Property
prop_groupWith = makeProp (Q.groupWith id) (groupWith id)

prop_map_groupWith :: [[Integer]] -> Property
prop_map_groupWith = makeProp (Q.map (Q.groupWith id)) (map (groupWith id))
                     
prop_groupWith_length :: [[Integer]] -> Property
prop_groupWith_length = makeProp (Q.groupWith Q.length) (groupWith length)

prop_sortWith  :: [Integer] -> Property
prop_sortWith = makeProp (Q.sortWith id) (sortWith id)

prop_map_sortWith :: [[Integer]] -> Property
prop_map_sortWith = makeProp (Q.map (Q.sortWith id)) (map (sortWith id))

prop_map_sortWith_length :: [[[Integer]]] -> Property
prop_map_sortWith_length = makeProp (Q.map (Q.sortWith Q.length)) (map (sortWith length))
                           
prop_map_groupWith_length :: [[[Integer]]] -> Property
prop_map_groupWith_length = makeProp (Q.map (Q.groupWith Q.length)) (map (groupWith length))

prop_sortWith_length_nest  :: [[[Integer]]] -> Property
prop_sortWith_length_nest = makeProp (Q.sortWith Q.length) (sortWith length)
                            
prop_groupWith_length_nest :: [[[Integer]]] -> Property
prop_groupWith_length_nest = makeProp (Q.groupWith Q.length) (groupWith length)

prop_null :: [Integer] -> Property
prop_null = makeProp Q.null null

prop_map_null :: [[Integer]] -> Property
prop_map_null = makeProp (Q.map Q.null) (map null)

prop_length :: [Integer] -> Property
prop_length = makeProp Q.length (fromIntegral . length)

prop_length_tuple :: [(Integer, Integer)] -> Property
prop_length_tuple = makeProp Q.length (fromIntegral . length)

prop_map_length :: [[Integer]] -> Property
prop_map_length = makeProp (Q.map Q.length) (map (fromIntegral . length))

prop_map_minimum :: [[Integer]] -> Property
prop_map_minimum ps = and (map (\p -> length p > 0) ps)  
        ==>
    makeProp (Q.map Q.minimum) (map (fromIntegral . minimum)) ps

prop_map_maximum :: [[Integer]] -> Property
prop_map_maximum ps = and (map (\p -> length p > 0) ps)  
        ==>
    makeProp (Q.map Q.maximum) (map (fromIntegral . maximum)) ps

prop_map_map_minimum :: [[[Integer]]] -> Property
prop_map_map_minimum ps = and (map (and . map (\p -> length p > 0)) ps)  
        ==>
    makeProp (Q.map (Q.map Q.minimum)) (map (map(fromIntegral . minimum))) ps

prop_map_map_maximum :: [[[Integer]]] -> Property
prop_map_map_maximum ps = and (map (and . map (\p -> length p > 0)) ps)  
        ==>
    makeProp (Q.map (Q.map Q.maximum)) (map (map(fromIntegral . maximum))) ps


prop_map_length_tuple :: [[(Integer, Integer)]] -> Property
prop_map_length_tuple = makeProp (Q.map Q.length) (map (fromIntegral . length))

prop_reverse :: [Integer] -> Property
prop_reverse = makeProp Q.reverse reverse

prop_reverse_nest :: [[Integer]] -> Property
prop_reverse_nest = makeProp Q.reverse reverse

prop_map_reverse :: [[Integer]] -> Property
prop_map_reverse = makeProp (Q.map Q.reverse) (map reverse)

prop_map_reverse_nest :: [[[Integer]]] -> Property
prop_map_reverse_nest = makeProp (Q.map Q.reverse) (map reverse)

prop_and :: [Bool] -> Property
prop_and = makeProp Q.and and

prop_map_and :: [[Bool]] -> Property
prop_map_and = makeProp (Q.map Q.and) (map and)

prop_map_map_and :: [[[Bool]]] -> Property
prop_map_map_and = makeProp (Q.map (Q.map Q.and)) (map (map and))

prop_or :: [Bool] -> Property
prop_or = makeProp Q.or or

prop_map_or :: [[Bool]] -> Property
prop_map_or = makeProp (Q.map Q.or) (map or)

prop_map_map_or :: [[[Bool]]] -> Property
prop_map_map_or = makeProp (Q.map (Q.map Q.or)) (map (map or))

prop_any_zero :: [Integer] -> Property
prop_any_zero = makeProp (Q.any (Q.== 0)) (any (== 0))

prop_map_any_zero :: [[Integer]] -> Property
prop_map_any_zero = makeProp (Q.map (Q.any (Q.== 0))) (map (any (== 0)))

prop_all_zero :: [Integer] -> Property
prop_all_zero = makeProp (Q.all (Q.== 0)) (all (== 0))

prop_map_all_zero :: [[Integer]] -> Property
prop_map_all_zero = makeProp (Q.map (Q.all (Q.== 0))) (map (all (== 0)))

prop_sum_integer :: [Integer] -> Property
prop_sum_integer = makeProp Q.sum sum

prop_map_sum :: [[Integer]] -> Property
prop_map_sum = makeProp (Q.map Q.sum) (map sum)

prop_map_map_sum :: [[[Integer]]] -> Property
prop_map_map_sum = makeProp (Q.map (Q.map Q.sum)) (map (map sum))

prop_sum_double :: [Double] -> Property
prop_sum_double = makePropDouble Q.sum sum

prop_concat :: [[Integer]] -> Property
prop_concat = makeProp Q.concat concat
              
prop_map_concat :: [[[Integer]]] -> Property
prop_map_concat = makeProp (Q.map Q.concat) (map concat)

prop_concatMap :: [Integer] -> Property
prop_concatMap = makeProp (Q.concatMap Q.singleton) (concatMap (\a -> [a]))

prop_maximum :: [Integer] -> Property
prop_maximum = makePropNotNull Q.maximum maximum

prop_minimum :: [Integer] -> Property
prop_minimum = makePropNotNull Q.minimum minimum

prop_splitAt :: (Integer, [Integer]) -> Property
prop_splitAt = makeProp (uncurryQ Q.splitAt) (\(a,b) -> splitAt (fromIntegral a) b)

prop_takeWhile :: (Integer, [Integer]) -> Property
prop_takeWhile = makeProp (uncurryQ $ Q.takeWhile . (Q.==))
                          (uncurry  $   takeWhile . (==))

prop_dropWhile :: (Integer, [Integer]) -> Property
prop_dropWhile = makeProp (uncurryQ $ Q.dropWhile . (Q.==))
                          (uncurry  $   dropWhile . (==))

prop_map_takeWhile :: (Integer, [[Integer]]) -> Property
prop_map_takeWhile = makeProp (\z -> Q.map (Q.takeWhile (Q.fst z Q.==)) (Q.snd z)) 
                              (\z -> map (takeWhile (fst z ==)) (snd z))

prop_map_dropWhile :: (Integer, [[Integer]]) -> Property
prop_map_dropWhile = makeProp (\z -> Q.map (Q.dropWhile (Q.fst z Q.==)) (Q.snd z)) 
                              (\z -> map (dropWhile (fst z ==)) (snd z))

prop_span :: (Integer, [Integer]) -> Property
prop_span = makeProp (uncurryQ $ Q.span . (Q.==))
                     (uncurry   $   span . (==) . fromIntegral)

prop_break :: (Integer, [Integer]) -> Property
prop_break = makeProp (uncurryQ $ Q.break . (Q.==))
                     (uncurry   $   break . (==) . fromIntegral)

prop_elem :: (Integer, [Integer]) -> Property
prop_elem = makeProp (uncurryQ $ Q.elem)
                     (uncurry  $   elem)

prop_notElem :: (Integer, [Integer]) -> Property
prop_notElem = makeProp (uncurryQ $ Q.notElem)
                        (uncurry  $   notElem)

prop_lookup :: (Integer, [(Integer,Integer)]) -> Property
prop_lookup = makeProp (uncurryQ $ Q.lookup)
                       (uncurry  $   lookup)

prop_zip :: ([Integer], [Integer]) -> Property
prop_zip = makeProp (uncurryQ Q.zip) (uncurry zip)

prop_map_zip :: ([Integer], [[Integer]]) -> Property
prop_map_zip = makeProp (\z -> Q.map (Q.zip $ Q.fst z) $ Q.snd z) (\(x, y) -> map (zip x) y)


prop_zipWith :: ([Integer], [Integer]) -> Property
prop_zipWith = makeProp (uncurryQ $ Q.zipWith (+)) (uncurry $ zipWith (+))

prop_unzip :: [(Integer, Integer)] -> Property
prop_unzip = makeProp Q.unzip unzip

prop_map_unzip :: [[(Integer, Integer)]] -> Property
prop_map_unzip = makeProp (Q.map Q.unzip) (map unzip)

prop_nub :: [Integer] -> Property
prop_nub = makeProp Q.nub nub

prop_map_nub :: [[(Integer, Integer)]] -> Property
prop_map_nub = makeProp (Q.map Q.nub) (map nub)

-- * Tuples

prop_fst :: (Integer, Integer) -> Property
prop_fst = makeProp Q.fst fst
           
prop_map_fst :: [(Integer, Integer)] -> Property
prop_map_fst = makeProp (Q.map Q.fst) (map fst)

prop_snd :: (Integer, Integer) -> Property
prop_snd = makeProp Q.snd snd
           
prop_map_snd :: [(Integer, Integer)] -> Property
prop_map_snd = makeProp (Q.map Q.snd) (map snd)

-- * Numerics

prop_add_integer :: (Integer,Integer) -> Property
prop_add_integer = makeProp (uncurryQ (+)) (uncurry (+))

prop_add_double :: (Double,Double) -> Property
prop_add_double = makePropDouble (uncurryQ (+)) (uncurry (+))

prop_mul_integer :: (Integer,Integer) -> Property
prop_mul_integer = makeProp (uncurryQ (*)) (uncurry (*))

prop_mul_double :: (Double,Double) -> Property
prop_mul_double = makePropDouble (uncurryQ (*)) (uncurry (*))

prop_div_double :: (Double,Double) -> Property
prop_div_double (x,y) =
      y /= 0
  ==> makePropDouble (uncurryQ (/)) (uncurry (/)) (x,y)

prop_integer_to_double :: Integer -> Property
prop_integer_to_double = makePropDouble Q.integerToDouble fromInteger

prop_map_integer_to_double :: [Integer] -> Property
prop_map_integer_to_double = makePropListDouble (Q.map Q.integerToDouble) (map fromInteger)

prop_abs_integer :: Integer -> Property
prop_abs_integer = makeProp Q.abs abs

prop_abs_double :: Double -> Property
prop_abs_double = makePropDouble Q.abs abs

prop_signum_integer :: Integer -> Property
prop_signum_integer = makeProp Q.signum signum

prop_signum_double :: Double -> Property
prop_signum_double = makePropDouble Q.signum signum

prop_negate_integer :: Integer -> Property
prop_negate_integer = makeProp Q.negate negate

prop_negate_double :: Double -> Property
prop_negate_double = makePropDouble Q.negate negate
