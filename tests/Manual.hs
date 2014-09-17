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

data Packet = Packet
    { p_dest :: Integer
    , p_len  :: Integer
    , p_pid  :: Integer
    , p_src  :: Integer
    , p_ts   :: Integer
    }

deriveDSH ''Packet
deriveTA ''Packet
generateTableSelectors ''Packet

packets :: Q [Packet]
packets = table "packets" $ TableHints [ Key ["p_pid"]
                                       , Key ["p_src", "p_dest", "p_ts"]
                                       ] NonEmpty

--------------------------------------------------------------------------------
-- Flow statistics

deltas :: Q [Integer] -> Q [Integer]
deltas xs = cons 0 (map (\(view -> (a, b)) -> a - b) (zip (drop 1 xs) xs))

-- TRY OUT: better or worse than drop?
deltas' :: Q [Integer] -> Q [Integer]
deltas' xs = cons 0
             [ ts - ts'
             | (view -> (ts, i))   <- number xs
             , (view -> (ts', i')) <- number xs
             , i' == i - 1
             ]


sums :: (QA a, Num a) => Q [a] -> Q [a]
sums as = [ sum [ a' | (view -> (a', i')) <- nas, i' <= i ]
          | let nas = number as
	  , (view -> (a, i)) <- nas
	  ]

-- | For each packet, compute the ID of the flow that it belongs to
flowids :: Q [Packet] -> Q [Integer]
flowids ps = sums [ if d > 120 then 1 else 0 | d <- deltas $ map p_tsQ ps ]

-- | For each flow, compute the number of packets and average length
-- of packets in the flow. A flow is defined as a number of packets
-- between the same source and destination in which the time gap
-- between consecutive packets is smaller than 120ms.
flowStats :: Q [(Integer, Integer, Integer, Double)]
flowStats = [ tuple4 src 
                     dst 
                     (length g)
                     (avg $ map (p_lenQ . fst) g)
            | (view -> (k, g)) <- flows
            , let (view -> (src, dst, _)) = k
            ]
  where
    flows = groupWithKey (\p -> tuple3 (p_srcQ $ fst p) (p_destQ $ fst p) (snd p)) 
                         $ zip packetsOrdered (flowids packetsOrdered)

    packetsOrdered = sortWith (\p -> tuple3 (p_srcQ p) (p_destQ p) (p_tsQ p)) packets

    

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
    trades' = filter (\t -> t_tidQ t == toQ stock && t_tradeDateQ t == toQ date) 
              $ sortWith t_timestampQ trades

c1 :: Q [[Integer]]
c1 = [ [ x + y | y <- toQ [10, 20] ] | x <- toQ [1, 2] ]

c2 :: Q [[[Integer]]]
c2 = [ [ [ x + y + z | z <- toQ [100, 200] ] | y <- toQ [10, 20] ] | x <- toQ [1, 2] ]

q1 :: Q [(Integer, Integer)]
q1 = 
  [ tuple2 x y
  | x <- fst xs
  , y <- snd xs
  ]

  where xs = toQ ([0], [0])


main :: IO ()
main = getConn P.>>= \c -> debugQ "q" c q1
--main = debugQX100 "q" x100Conn $ q (toQ [1..50])
--main = debugQX100 "q1" x100Conn q1
