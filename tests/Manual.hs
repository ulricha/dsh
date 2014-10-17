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

import qualified Data.Text as T

import TPCH

data Foo = Foo { foo1 :: Integer, foo2 :: Text, foo3 :: Integer }

deriveDSH ''Foo
deriveTA ''Foo
generateTableSelectors ''Foo

getConn :: IO Connection
getConn = connectPostgreSQL "user = 'au' password = 'foobar' host = 'localhost' port = '5432' dbname = 'aquery'"

x100Conn :: X100Info
x100Conn = undefined

bar :: Q [(Integer, Integer, Integer)]
bar = [ triple a c 42 | (view -> (a, b, c)) <- toQ ([(1,2,3), (4,5,6), (7,8,9)] :: [(Integer, Integer, Integer)]) ]

{-
li :: Q [(Integer, Text, Double)]
li = [ tup3 (l_linenumberQ l) (l_returnflagQ l) (l_discountQ l)
     | l <- lineitems
     , l_taxQ l > 5.0
     ]
-}

group' :: (QA a, QA b, TA b, Eq b) => (Q a -> Q b) -> Q [a] -> Q [(b, [a])]
group' p as =
    [ tup2 k [ a' | a' <- as, p a' == k ]
    | k <- nub $ map p as
    ]

q4'' =
  sortWith fst
  $ map (\(view -> (k, g)) -> pair k (length g)) 
  $ group' id
    [ o_orderpriorityQ o
    | o <- orders
    , o_orderdateQ o >= 42
    , o_orderdateQ o < 42 + 57
    , hasOverdueItem o
    ]

data Interval = Interval { iv_start :: Integer, iv_end :: Integer }

-- | Is at least one of the orders' items overdue?
hasOverdueItem :: Q Order -> Q Bool
hasOverdueItem o = or [ l_commitdateQ l < l_receiptdateQ l
                      | l <- lineitems
                      , l_orderkeyQ l == o_orderkeyQ o
                      ]

-- | An order is problematic if at least one of its items was overdue.
problematicOrders :: Interval -> Q [Text]
problematicOrders interval =
    [ o_orderpriorityQ o
    | o <- orders
    , o_orderdateQ o >= toQ (iv_start interval)
    , o_orderdateQ o < toQ (iv_end interval)
    , hasOverdueItem o
    ]

-- | Compute the number of problematic orders per priority level.
q4'''' :: Interval -> Q [(Text, Integer)]
q4'''' interval =
    [ tup2 op (length $ filter (== op) oids)
    | op <- nub oids
    ]
  where
    oids = problematicOrders interval

-- | Compute all orders for a given customer that do not fall into
-- certain categories.
custOrders :: Q Customer -> Q [Order]
custOrders c = [ o 
               | o <- orders
               , c_custkeyQ c == o_custkeyQ o
               , not $ o_commentQ o `like` "%WORD1%WORD2"
               ]

-- | Compute number of orders per customer, including those that have
-- not placed any orders.
ordersPerCustomer :: Q [(Integer, Integer)]
ordersPerCustomer =
    [ tup2 (c_custkeyQ c) (length $ custOrders c)
    | c <- customers
    ]

-- | TPC-H Q13: Distribution of orders per customer, including
-- customers without orders.
q13 :: Q [(Integer, Integer)]
q13 = 
    reverse $ sortWith id $
    [ tup2 c_count (length g)
    | (view -> (c_count, g)) <- groupWithKey snd ordersPerCustomer
    ]


hasNationality :: Q Customer -> Text -> Q Bool
hasNationality c nationName = any (\n -> n_nameQ n == toQ nationName
                                         && 
                                         c_nationkeyQ c == n_nationkeyQ n) 
                                  nations

revenue :: Q Order -> Q Double
revenue o = sum [ l_extendedpriceQ l * (1 - l_discountQ l)
                    | l <- lineitems
                    , l_orderkeyQ l == o_orderkeyQ o
                    ]

nestedStuff :: Q [(Text, [(Integer, Double)])]
nestedStuff =
    [ tup2 (c_nameQ c) [ tup2 (o_orderdateQ o) (revenue o)
                       | o <- orders
                       , o_custkeyQ o == c_custkeyQ c
                       , o_orderstatusQ o == toQ "PENDING"
                       ]
    | c <- customers
    , c `hasNationality` "GERMANY"
    ]

nj2 :: Q [(Integer, [Integer])]
nj2 = 
    [ pair x [ y | y <- toQ [3,4,5,6,3,6,4,1,1,1], x == y ]
    | x <- toQ [1,2,3,4,5,6]
    ]

data Trade = Trade
    { t_price     :: Double
    , t_tid       :: Integer
    , t_timestamp :: Integer
    , t_tradeDate :: Integer
    }

deriveDSH ''Trade
deriveTA ''Trade
generateTableSelectors ''Trade

data Portfolio = Portfolio
    { po_pid         :: Integer
    , po_tid         :: Integer
    , po_tradedSince :: Integer
    }

deriveDSH ''Portfolio
deriveTA ''Portfolio
generateTableSelectors ''Portfolio

trades :: Q [Trade]
trades = table "trades" $ TableHints [ Key ["t_tid", "t_timestamp"] ] NonEmpty

portfolios :: Q [Portfolio]
portfolios = table "portfolio" $ TableHints [Key ["po_pid"] ] NonEmpty

--------------------------------------------------------------------------------
-- For a given date and stock, compute the best profit obtained by
-- buying the stock and selling it later.

-- | For each list element, compute the minimum of all elements up to
-- the current one.
mins :: (Ord a, QA a, TA a) => Q [a] -> Q [a]
mins as = [ minimum [ a' | (view -> (a', i')) <- nas, i' <= i ]
          | let nas = number as
	  , (view -> (a, i)) <- nas
	  ]   

bestProfit :: Integer -> Integer -> Q Double
bestProfit stock date = 
    maximum [ t_priceQ t - minPrice
            | (view -> (t, minPrice)) <- zip trades' (mins $ map t_priceQ trades')
            ]
                                  
  where
    trades' = filter (\t -> t_tidQ t == toQ stock && t_tradeDateQ t == toQ date) 
              $ sortWith t_timestampQ trades
    
--------------------------------------------------------------------------------
-- Compute the ten last stocks for each quote in a portfolio.

lastn :: QA a => Integer -> Q [a] -> Q [a]
lastn n xs = drop (length xs - toQ n) xs

last10 :: Integer -> Q [(Integer, [Double])]
last10 portfolio = 
    map (\(view -> (tid, g)) -> pair tid (map snd $ lastn 10 g))
    $ groupWithKey fst
    [ pair (t_tidQ t) (t_priceQ t)
    | t <- trades
    , p <- portfolios
    , t_tidQ t == po_tidQ p
    , po_pidQ p == toQ portfolio
    ]

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
packets = table "packets" $ TableHints [ Key ["p_pid"]] NonEmpty

--------------------------------------------------------------------------------
-- Flow statistics

-- | Positional aligning via zip
deltasZip :: Q [Integer] -> Q [Integer]
deltasZip xs = cons 0 (map (\(view -> (a, b)) -> a - b) (zip (drop 1 xs) xs))
-- deltasZip xs = cons 0 [ a - b | a <- drop 1 xs | b <- xs ]

-- | Aligning with an explicit (order-preserving) self join
deltasSelfJoin :: Q [Integer] -> Q [Integer]
deltasSelfJoin xs = cons 0 [ ts - ts'
                           | (view -> (ts, i))   <- number xs
                           , (view -> (ts', i')) <- number xs
                           , i' == i - 1
                           ]

-- | Aligning using a nested self join. Note that this is semantically
-- not equivalent to the other deltas: For each element we compute the
-- minimum of the element and its predecessor. If the input is ordered
-- by timestamps at least in a partitioned way, this will be OK.
deltasWin :: Q [Integer] -> Q [Integer]
deltasWin xs = [ ts - minimum [ ts' 
                             | (view -> (ts', i')) <- number xs
                             , i' >= i - 1
                             , i' <= i
                             ]
              | (view -> (ts, i)) <- number xs
              ]

deltasHead :: Q [Integer] -> Q [Integer]
deltasHead xs = [ ts - head [ ts' 
                            | (view -> (ts', i')) <- number xs
                            , i' >= i - 1
                            , i' <= i
                            ]
                | (view -> (ts, i)) <- number xs
                ]

sums :: (QA a, Num a) => Q [a] -> Q [a]
sums as = [ sum [ a' | (view -> (a', i')) <- nas, i' <= i ]
          | let nas = number as
	  , (view -> (a, i)) <- nas
	  ]

-- | For each packet, compute the ID of the flow that it belongs to
flowids :: (Q [Integer] -> Q [Integer]) -> Q [Packet] -> Q [Integer]
flowids deltaFun ps = sums [ if d > 120 then 1 else 0 | d <- deltaFun $ map p_tsQ ps ]

-- | For each flow, compute the number of packets and average length
-- of packets in the flow. A flow is defined as a number of packets
-- between the same source and destination in which the time gap
-- between consecutive packets is smaller than 120ms.
flowStats :: (Q [Integer] -> Q [Integer]) -> Q [(Integer, Integer, Integer, Double)]
flowStats deltaFun = 
    [ tup4 src 
           dst 
           (length g)
           (avg $ map (p_lenQ . fst) g)
    | (view -> (k, g)) <- flows
    , let (view -> (src, dst, _)) = k
    ]
  where
    flows = groupWithKey (\p -> tup3 (p_srcQ $ fst p) (p_destQ $ fst p) (snd p)) 
                         $ zip packetsOrdered (flowids deltaFun packetsOrdered)

    packetsOrdered = sortWith (\p -> tup3 (p_srcQ p) (p_destQ p) (p_tsQ p)) packets

{-

Cleaned up for presentation, the query could look like this:

flowStats :: (Q [Integer] -> Q [Integer]) -> Q [(Integer, Integer, Integer, Double)]
flowStats = 
    [ (src, dst, length g, avg $ map (p_lenQ . fst) g)
    | ((src, dst, _), g) <- flows
    ]
  where
    flows = groupWith (\(p, fid) -> (p_srcQ p, p_destQ p, fid) )
                      $ zip packetsOrdered (flowids packetsOrdered)

    packetsOrdered = sortWith (\p -> (p_srcQ p, p_destQ p, p_tsQ p)) packets
-}

flowStatsZip :: Q [(Integer, Integer, Integer, Double)]
flowStatsZip = flowStats deltasZip

flowStatsSelfJoin :: Q [(Integer, Integer, Integer, Double)]
flowStatsSelfJoin = flowStats deltasSelfJoin

flowStatsWin :: Q [(Integer, Integer, Integer, Double)]
flowStatsWin = flowStats deltasWin

flowStatsHead :: Q [(Integer, Integer, Integer, Double)]
flowStatsHead = flowStats deltasHead

    
main :: IO ()
-- main = getConn P.>>= \c -> debugQ "q" c $ qj3 $ toQ (([], [], []) :: ([Integer], [Integer], [Integer]))
-- main = getConn P.>>= \c -> debugQ "q" c foo
main = getConn P.>>= \c -> debugQ "q" c $ flowStatsHead
--main = debugQX100 "q" x100Conn $ q (toQ [1..50])
--main = debugQX100 "q1" x100Conn q1
