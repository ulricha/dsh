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

data Foo = Foo { foo1 :: Integer, foo2 :: Text, foo3 :: Integer }

deriveDSH ''Foo
deriveTA ''Foo
generateTableSelectors ''Foo

getConn :: IO Connection
getConn = connectPostgreSQL "user = 'au' password = 'foobar' host = 'localhost' port = '5432' dbname = 'tpch'"

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
    
main :: IO ()
-- main = getConn P.>>= \c -> debugQ "q" c $ qj3 $ toQ (([], [], []) :: ([Integer], [Integer], [Integer]))
-- main = getConn P.>>= \c -> debugQ "q" c foo
main = getConn P.>>= \c -> debugQ "q" c q13
--main = debugQX100 "q" x100Conn $ q (toQ [1..50])
--main = debugQX100 "q1" x100Conn q1
