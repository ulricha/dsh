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

import Database.HDBC.PostgreSQL

getConn :: IO Connection
getConn = connectPostgreSQL "user = 'au' password = 'foobar' host = 'localhost' port = '5432' dbname = 'au'"


x100Conn :: X100Info
x100Conn = undefined

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
data Trade = Trade
    { t_price     :: Double
    , t_tid       :: Text
    , t_timestamp :: Integer
    , t_tradeDate :: Integer
    }

deriveDSH ''Trade
deriveTA ''Trade
generateTableSelectors ''Trade

data Portfolio = Portfolio
    { po_pid         :: Integer
    , po_tid         :: Text
    , po_tradedSince :: Integer
    }

deriveDSH ''Portfolio
deriveTA ''Portfolio
generateTableSelectors ''Portfolio

trades :: Q [Trade]
trades = table "trades" $ TableHints [ Key ["t_tid", "t_timestamp"] ] NonEmpty

portfolios :: Q [Portfolio]
portfolios = table "portfolio" $ TableHints [Key ["po_pid"] ] NonEmpty


lastn :: QA a => Integer -> Q [a] -> Q [a]
lastn n xs = drop (length xs - toQ n) xs

last10 :: Integer -> Q [(Text, [Double])]
last10 portfolio = 
    map (\(view -> (tid, g)) -> pair tid (map snd $ lastn 10 g))
    $ groupWithKey fst
    [ pair (t_tidQ t) (t_priceQ t)
    | t <- trades
    , p <- portfolios
    , t_tidQ t == po_tidQ p
    , po_pidQ p == toQ portfolio
    ]


-- | For each list element, compute the minimum of all elements up to
-- the current one.
mins :: (Ord a, QA a) => Q [a] -> Q [a]
mins as = [ minimum [ a' | (view -> (a', i')) <- nas, i' <= i ]
          | let nas = number as
	  , (view -> (a, i)) <- nas
	  ]   

bestProfit :: Text -> Integer -> Q Double
bestProfit stock date = 
    maximum [ t_priceQ t - minPrice
            | (view -> (t, minPrice)) <- zip trades' (mins $ map t_priceQ trades')
            ]
                                  
  where
    trades' = filter (\t -> t_tidQ t == toQ stock && t_tradeDateQ t == toQ date) trades


main :: IO ()
main = getConn P.>>= \c -> debugQ "q" c $ bestProfit "ACME" 42
--main = debugQX100 "q" x100Conn $ q (toQ [1..50])
--main = debugQX100 "q1" x100Conn q1
