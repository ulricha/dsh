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

import TPCH

getConn :: IO Connection
getConn = connectPostgreSQL "user = 'au' password = 'foobar' host = 'localhost' port = '5432' dbname = 'tpch'"

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
mins :: (Ord a, QA a,TA a) => Q [a] -> Q [a]
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


{-
q1 :: Q [Integer]
q1 =
    let xs = (toQ [1, 2, 3, 4, 5, 6, 7] :: Q [Integer])
        ys = (toQ [2, 4, 6] :: Q [Integer])
    in [ x | x <- xs , x `elem` [ y | y <- ys, y < 6 ] ]
-}

q2 :: Q [Bool]
q2 = map or $ toQ [[False]]


q3 :: Q [Integer]
q3 = concatMap (\x -> cond ((>) x 0) (x <| (toQ [])) (toQ [])) $ toQ [0]



withFlagStatus :: Q LineItem -> Q (Text, Text)
withFlagStatus li = tuple2 (l_returnflagQ li) (l_linestatusQ li)

filteredItems :: Q [LineItem]
filteredItems = [ li | li <- lineitems , l_shipdateQ li <= 42 ]

fst9 :: (QA a, QA b, QA c, QA d, QA e, QA f, QA g, QA h, QA i) => Q (a, b, c, d, e, f, g, h, i) -> Q a
fst9 (view -> (a, _, _, _, _, _, _, _, _)) = a

q1 :: Q [((Text, Text), Double, Double, Double, Double, Double, Double, Double, Integer)]
q1 = sortWith fst9 $ 
     [ tuple9
	  k
	  (sum $ map l_quantityQ lis)
	  (sum $ map l_extendedpriceQ lis)
	  (sum $ map (\li -> l_extendedpriceQ li * (1 - l_discountQ li)) lis)
	  (sum $ map (\li -> l_extendedpriceQ li * (1 - l_discountQ li) * (1 + l_taxQ li)) lis)
	  (avg $ map l_quantityQ lis)
	  (avg $ map l_extendedpriceQ lis)
	  (avg $ map l_discountQ lis)
	  (length lis)
      | (view -> (k, lis)) <- groupWithKey withFlagStatus filteredItems
      ]

qs :: Q Integer
qs = 42 + sum [ 23 + x + sum [ x + y | y <- toQ [10, 20] ] | x <- toQ [1, 2] ]

qr :: Q [[Integer]]
qr = [ [ x * 42 | x <- take 23 xs ] | xs <- toQ [ [1,2,3,4], [10,20,30], [100,200,300,400] ] ]

qb :: Q [[Integer]]
-- qb = [ [ x * 42 | x <- xs ] | xs <- toQ [[1,2,3], [4,5] ]]
-- qb = [ [ x + length xs | x <- xs ] | xs <- toQ [[1,2,3], [4,5] ] ]
-- qb = [ [ x + y | y <- toQ [4, 5] ] | x <- toQ [1,2,3] ]
-- qb = [ [ [ x + length xs + length xss | x <- xs ] | xs <- xss ] | xss <- toQ [[[1,2], [3,4]], [[5], [6,7,8]]] ]
qb = [ [ x + length xs | x <- take (length xs - 3) xs ] | xs <- toQ [[1,2,3], [4,5]] ]

qj = 
    let xs = (toQ [1, 2, 3, 4, 5, 6, 7] :: Q [Integer])
        ys = (toQ [2, 4, 6] :: Q [Integer])
    in [ x | x <- xs , x `elem` [ y | y <- ys, y < 6 ] ]

njgxs1 :: [Integer]
njgxs1 = [1,2,3,4,5,6,7,8,12]

njgys1 :: [Integer]
njgys1 = [2,3,2,4,5,5,9,12,2,2,13]

njgzs1 :: [(Integer, Integer)]
njgzs1 = [(2, 20), (5, 60), (3, 30), (3, 80), (4, 40), (5, 10), (5, 30), (12, 120)]

hnjg1 =
  [ x
  | x <- toQ njgxs1
  , x < 8
  , sum [ snd z | z <- toQ njgzs1, fst z == x ] > 100
  ]

hcp (view -> (xs, ys)) = [ pair x y | x <- xs, y <- ys]

qj3 (view -> (xs, ys, zs)) = 
  [ tuple3 x y z
  | x <- xs
  , y <- ys
  , z <- zs
  , x == y
  , y == z
  ]

aj12 = 
    let xs = toQ ([6,7,8,9,10,12] :: [Integer])
        ys = toQ ([8,9,12,13,15,16] :: [Integer])
    in [ x | x <- xs, and [ x < y | y <- ys, y > 10 ]]

aj_class12 :: Q ([Integer], [Integer]) -> Q [Integer]
aj_class12 (view -> (xs, ys)) = 
  [ x 
  | x <- xs
  , and [ x == y | y <- ys, y > 10 ]
  ]

qif = [ if x > 5 then x + 42 else x * 2 | x <- toQ ([1..10] :: [Integer])]

qx = map (map sum) $ toQ ([[]] :: [[[Integer]]])

qf = [ x | x <- toQ ([1..10] :: [Integer]), x < 5 ]

project 
  :: Q ((Integer, Integer, Integer), [((Integer, Integer, Integer), (Double, Double))])
  -> Q ((Integer, Integer, Integer), Double)
project gk = pair (fst gk) revenue
  where
    revenue = sum [ ep * (1 - d) | (view -> (ep, d)) <- [ snd x | x <- snd gk ] ]
    
byRevDate :: Q ((Integer, Integer, Integer), Double) -> Q (Double, Integer)
byRevDate (view -> (((view -> (_, _, sp)), r))) = pair (r * (-1)) sp

q3t :: Q [((Integer, Integer, Integer), Double)]
q3t =
  sortWith byRevDate $
  map project $
  groupWithKey fst $
  [ let sep = tuple3 (l_orderkeyQ l) (o_orderdateQ o) (o_shippriorityQ o)
    in pair sep (pair (l_extendedpriceQ l) (l_discountQ l))
  | c <- customers
  , o <- orders
  , l <- lineitems
  , c_mktsegmentQ c == (toQ "foo")
  , c_custkeyQ c == o_custkeyQ o
  , l_orderkeyQ l == o_orderkeyQ o
  , o_orderdateQ o < (toQ 42)
  , l_shipdateQ l > (toQ 23)
  ]

foo :: Q [(Integer, [Integer])]
foo = 
    [ pair x [ y | y <- toQ [3,4,5,6,3,6,4,1,1,1], x == y ]
    | x <- toQ [1,2,3,4,5,6]
    ]

main :: IO ()
-- main = getConn P.>>= \c -> debugQ "q" c $ qj3 $ toQ (([], [], []) :: ([Integer], [Integer], [Integer]))
-- main = getConn P.>>= \c -> debugQ "q" c foo
main = getConn P.>>= \c -> runQ c foo P.>>= \r -> putStrLn $ show r
--main = debugQX100 "q" x100Conn $ q (toQ [1..50])
--main = debugQX100 "q1" x100Conn q1
