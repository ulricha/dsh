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

import Database.HDBC.PostgreSQL

getConn :: Connection
getConn = undefined

xs :: Q [(Integer, Integer)]
xs = toQ [(3,5),(4,6),(5,7),(6,9)]

ys :: Q [Integer]
ys = toQ [1,2,3,4]

zs :: Q [Integer]
zs = toQ [1..20]

ns1 :: Q [(Integer, [Integer])]
ns1 = toQ [(1, [10, 20])]

ns2 :: Q [(Integer, [Integer])]
ns2 = toQ [(2, [20, 30])]


{-
q :: Q [Integer]
q = [ x
    | x <- xs
    , and [ x >= y | y <- ys, x /= y ]
    ]
-}

{-
q :: Q [Integer]
q =
    let xs = (toQ [1, 2, 3, 4, 5, 6, 7] :: Q [Integer])
        ys = (toQ [2, 4, 6, 7] :: Q [Integer])
    in [ x | x <- xs , not $ x `elem` [ y | y <- ys, y < 5 ] ]

npv :: Q [(Integer, Integer)]
npv = 
    [ x
    | x <- xs
    , y <- ys
    , z <- zs
    , fst x == y
    , y == z
    , z == 5
    ]

tv :: Q Integer
tv = 42 * sum 
    [ fst x
    | x <- xs
    , y <- ys
    , z <- zs
    , fst x == y
    , y == z
    , z == 5
    ]

pv :: Q [(Integer, Integer)] -> Q Integer
pv g = sum [ x1 * x2 | (view -> (x1, x2)) <- g]

q11 :: Q [(Integer, Integer)]
q11 = [ pair k (pv g)
      | (view -> (k, g)) <- groupWithKey fst npv
      , pv g > tv
      ]
-}

q :: Q [Integer]
q = [ x 
    | xs <- toQ [[1,2,3],[4,5,6]]
    , x <- xs
    , x == length xs
    ]

{-
q :: Q [(Integer, Integer)]
q = [ pair y z | y <- ys, z <- zs ]
-}

{-
q :: Q [(Integer, Integer)]
q = [ pair (fst x) (fst y)
    | x <- ns1
    , y <- ns2
    , length (snd x) == length (snd y)
    ]
-}

{-
mins :: (Ord a, QA a) => Q [a] -> Q [a]
mins as = [ minimum [ a' | (view -> (a', i')) <- number as, i' <= i ]
	  | (view -> (a, i)) <- number as
	  ]   

q :: Q [Integer] -> Q Integer
q is = maximum [ i - i' | (view -> (i, i')) <- zip is' (mins is') ]
  where is' = filter (\i -> i > 15 && i < 42) is

trades :: Q [(Integer, Integer)]
trades = toQ [(42, 10)]

portfolio :: Q [Integer]
portfolio = toQ [23, 2]

lastn :: QA a => Integer -> Q [a] -> Q [a]
lastn n xs = drop (length xs - toQ n) xs

q1 = map (\(view -> (tid, g)) -> pair tid (map snd $ lastn 10 g))
     $ groupWithKey fst
         [ pair tid tprice
         | (view -> (tid, tprice)) <- trades
         , tid' <- portfolio
         , tid == tid'
         ]

-}

{-
mins :: (Ord a, QA a) => Q [a] -> Q [a]
mins as = [ minimum [ a' | (a', i') <- number as, i' <= i ]
	  | (a, i) <- number as
	  ]   

q :: Q [Integer] -> Q Integer
q is = maximum [ i - i' | (i, i') <- zip is' (mins is') ]
  where is' = filter (\i -> i > 15 && i < 42) is
-}
    

main :: IO ()
main = debugQ "q" getConn $ q
--main = debugQX100 "q" x100Conn $ q (toQ [1..50])
--main = debugQX100 "q1" x100Conn q1
