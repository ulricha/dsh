{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MonadComprehensions   #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RebindableSyntax      #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}

module Main where

import qualified Prelude as P
import Database.DSH
import Database.DSH.Compiler

import Database.X100Client

--------------------------------------------------------------------
-- Complex vectors stored in base tables

fst3 :: (QA a, QA b, QA c) => Q (a, b, c) -> Q a
fst3 (view -> (a, _, _)) = a

vec :: String -> Q [(Integer, Double, Double)]
vec n = table n (defaultHints { keysHint = [Key ["pos"]], nonEmptyHint = NonEmpty })

vecFromTable :: Q [(Integer, Double, Double)] -> Q [Complex]
vecFromTable tab = map (\(view -> (_, i, r)) -> pair r i) $ sortWith fst3 tab

--------------------------------------------------------------------
-- Helpers, type definitions

if' :: Bool -> a -> a -> a
if' True  x _ = x
if' False _ y = y

-- * Complex numbers

type Complex = (Double, Double)

-- | Construction of complex values
(|+) :: Q Double -> Q Double -> Q Complex
(|+) = pair

-- | Complex multiplication
-- (a+bi)*(c+di) = (a*c - b*d)+(b*c + c*d)i
(.*) :: Q Complex -> Q Complex -> Q Complex
x .* y = (a*c - b * d) |+ (b*c - c*d)
  where
    (a, b) = view x
    (c, d) = view y

real :: Q Complex -> Q Double
real = fst

img :: Q Complex -> Q Double
img = snd

-- | Matrix transposition
φ :: QA a => Q [[a]] -> Q [[a]]
φ = transpose

-- | Array reshaping
ρ :: QA a => Integer -> Q [a] -> Q [[a]]
ρ = reshape

iArray :: QA a => Q [a] -> Q [Integer]
iArray v = map snd $ number0 v

number0 :: QA a => Q [a] -> Q [(a, Integer)]
number0 v = map (\x -> pair (fst x) ((snd x) - 1)) $ number v

cis :: Q Double -> Q Complex
cis r = cos r |+ sin r

ω :: Integer -> Q Integer -> Q Complex
ω n i = cis $ (2 * pi * integerToDouble i) / (fromIntegral n)

sumC :: Q [Complex] -> Q Complex
sumC cs = (sum $ map real cs) |+ (sum $ map img cs)

--------------------------------------------------------------------
-- Actual DFT implementations on dense vector representation

dft :: Integer -> Q [Complex] -> Q [Complex]
dft dim v = 
  [ sumC [ ω dim (i * j) .* x | (view -> (x, j)) <- number0 v ]
  | i <- iArray v
  ]

dftFast :: Integer -> Integer -> Q [Complex] -> Q [Complex]
dftFast m n v =
  concat [ map sumC $ φ [ [ ω (m * n) (a * (toQ n * d + c)) .* t
                          | (view -> (t, c)) <- number0 $ dft n z
                          ]
                        | (view -> (z, a)) <- number0 $ φ $ ρ m v
                        ]
         | d <- toQ [ 0 .. m - 1 ]
         ] 

dftFastRec1 :: Integer -> Integer -> Q [Complex] -> Q [Complex]
dftFastRec1 m n v =
  concat [ map sumC $ φ [ [ ω (m * n) (a * (toQ n * d + c)) .* t
                          | (view -> (t, c)) <- number0 $ dftFast m (n `P.div` m) z
                          ]
                        | (view -> (z, a)) <- number0 $ φ $ ρ m v
                        ]
         | d <- toQ [ 0 .. m - 1 ]
         ] 

dftFastRec :: Integer -> Integer -> Q [Complex] -> Q [Complex]
dftFastRec m n v =
  if' (m P.* n P.< 32)
    (dft (m P.* n) v)
    (concat [ map sumC $ φ [ [ ω (m * n) (a * (toQ n * d + c)) .* t
                             | (view -> (t, c)) <- number0 $ dftFastRec 2 (n `P.div` 2) z
                             ]
                           | (view -> (z, a)) <- number0 $ φ $ ρ m v
                           ]
            | d <- toQ [ 0 .. m - 1 ]
            ])

dftFastRecD :: Integer -> Integer -> Integer -> Q [Complex] -> Q [Complex]
dftFastRecD maxDepth = go 1
            
  where
    go :: Integer -> Integer -> Integer -> Q [Complex] -> Q [Complex]
    go depth m n v =
        if' (depth P.== maxDepth)
            (dft (m P.* n) v)
            (concat [ map sumC $ φ [ [ ω (m * n) (a * (toQ n * d + c)) .* t
                                     | (view -> (t, c)) <- number0 $ go (depth P.+ 1) m (n `P.div` m) z
                                     ]
                                   | (view -> (z, a)) <- number0 $ φ $ ρ m v
                                   ]
                    | d <- toQ [ 0 .. m - 1 ]
                    ])

---------------------------------------------------------------------
-- Sparse vector implementation

-- FIXME assume here that groupWith keeps order in partitions stable,
-- i.e. sorts by pos. That might currently not be the case.
-- reshapeSparse :: QA a => Integer -> Q [(Int, a)] -> Q [(Int, [(Int, a)])]
-- reshapeSparse n vec = 
--     -- Generate new indices for the outer vector
--     number 
--     -- Generate new indices for the inner vectors
--     $ map number 
--     -- Throw away old vector indices
--     $ map (map snd) 
--     $ groupWith byPos $ number vec
-- 
--   where
--     byPos :: QA a => Q (Integer, a) -> Q Integer
--     byPos v = ((fst v) - 1) / n

{-

type SparseVector a = [(Integer, a)]

type Row a = (Integer, Integer, a)
 
type SparseMatrix a = [Row a]

row :: QA a => Q (Row a) -> Q Integer
row (view -> (r, _, _)) = r

rowVec :: QA a => Q Integer -> Q (SparseMatrix a) -> Q (SparseVector a)
rowVec r m = [ pair c x | (view -> (r', c, x)) <- m, r == r' ]

reshape2 :: QA a => Integer -> Q (SparseVector a) -> Q (SparseMatrix a)
reshape2 n v = 
  [ tuple3 (p `div` (toQ n)) (p `mod` (toQ n)) x
  | (view -> (p, x)) <- v
  ]

transpose2 :: QA a => Q (SparseMatrix a) -> Q (SparseMatrix a)
transpose2 m =
  [ tuple3 c r x
  | (view -> (r, c, x)) <- m
  ]

dftSparse :: Integer -> Q (SparseVector Double) -> Q (SparseVector Double)
dftSparse dim v = 
  [ pair i (sum $ map snd xs)
  | (view -> (i, xs)) <- groupWithKey fst 
                                   [ pair i (ω dim (i * j) * x)
                                   | i <- (map fst v)
                                   , (view -> (j, x)) <- v
                                   ]
  ]

-- dftFastSparse :: Integer -> Integer -> Q (SparseVector Double) -> Q (SparseVector Double)
-- dftFastSparse m n v
--   [ [ 
--     | (view -> (t, c)) <- dftSparse $ dftrowVec a w
--     ]
--   | d <- toQ [ 0 .. m - 1 ]
--   , let w = transpose2 $ reshape2 n v
--   , a <- nub $ map row w
--   ]

-}

--------------------------------------------------------------------
-- Test cases

vec1 :: Q [Complex]
vec1 = toQ [ (1.0, 0.0)
           , (0.0, 0.0)
           , (0.0, 0.0)
           , (0.0, 0.0)
           , (0.0, 0.0)
           , (0.0, 0.0)
           , (0.0, 0.0)
           , (0.0, 0.0)
           ]

vec2 :: Q [Complex]
vec2 = toQ [ (0.0, 0.0)
           , (1.0, 0.0)
           , (0.0, 0.0)
           , (0.0, 0.0)
           , (0.0, 0.0)
           , (0.0, 0.0)
           , (0.0, 0.0)
           , (0.0, 0.0)
           ]

vec3 :: Q [Complex]
vec3 = toQ [ (1, 10)
           , (2, 20)
           , (3, 30)
           , (4, 40)
           , (5, 50)
           , (6, 60)
           , (7, 70)
           , (8, 80)
           ]

-- getConn :: IO Connection
-- getConn = connectPostgreSQL "user = 'au' password = 'foobar' host = 'localhost' port = '5432' dbname = 'tpch'"

getConnX100 :: X100Info
getConnX100 = x100Info "localhost" "48130" Nothing

{-
debugQ :: QA a => String -> Q a -> IO ()
debugQ prefix q = getConnX100 P.>>= \conn -> (debugX100VLOpt prefix conn q P.>> debugX100 prefix conn q)

execX100 :: (Show a, QA a) => Q a -> IO ()
execX100 q = getConnX100 P.>>= \conn -> runQX100 conn q P.>>= \r -> putStrLn P.$ P.show r
-}

main :: IO ()
main =
    --debugQX100 "dft_1024" getConnX100 (dft 1024 (vecFromTable $ vec "v1_1024"))
    -- P.>>
    -- debugQX100 "dftfast_1024" getConnX100 (dftFast 32 32 (vecFromTable $ vec "v1_1024"))
    debugQX100 "dftfast_16" getConnX100 (dftFast 32 2048 (vecFromTable $ vec "v1_2_16"))
    -- debugQ "dftfast_1024" (dftFast 32 32 (vecFromTable $ vec "v1_1024"))
    -- debugQ "dftfast_1024" (dftFast 2 512 (vecFromTable $ vec "v1_1024"))
    -- P.>>
    -- debugQ "dftfast1_1024" (dftFastRec1 16 64 (vecFromTable $ vec "v1_1024"))
    -- P.>>
    -- debugQ "dftfastrec_1024" (dftFastRec 2 512 (vecFromTable $ vec "v1_1024"))
    -- P.>>
    -- debugQ "dftfastrec_1024" (dftFastRecD 3 8 128 (vecFromTable $ vec "v1_1024"))
{-
    debugQVL "dft" (dft 8 vec1)
    P.>>
    debugQX100 "dft" (dft 8 vec1)
    P.>>
    debugQVL "dftFast" (dftFast 2 4 vec3)
    P.>>
    debugQX100 "dftFast" (dftFast 2 4 vec3)
    P.>>
    execX100 (dft 8 vec2)
    P.>>
    execX100 (dftFast 2 4 vec2)
-}
