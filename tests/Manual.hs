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
getConn = connectPostgreSQL "user = 'au' password = 'foobar' host = 'localhost' port = '5432' dbname = 'tpch'"

x100Conn :: X100Info
x100Conn = x100Info "localhost" "48130" Nothing

bar :: Q [(Integer, Integer, Integer)]
bar = [ triple a c 42 | (view -> (a, b, c)) <- toQ ([(1,2,3), (4,5,6), (7,8,9)] :: [(Integer, Integer, Integer)]) ]

{-
li :: Q [(Integer, Text, Double)]
li = [ tup3 (l_linenumberQ l) (l_returnflagQ l) (l_discountQ l)
     | l <- lineitems
     , l_taxQ l > 5.0
     ]
-}

data Range = Range { start :: Integer, end :: Integer }

deriveDSH ''Range

avgBalance :: Q [Customer] -> Q Double
avgBalance cs =
  avg [ c_acctbalQ c | c <- cs, c_acctbalQ c > 0.0 ]

ordersOf :: Q Customer -> Q [Order]
ordersOf c =
  [ o | o <- orders, o_custkeyQ o == c_custkeyQ c ]

potentialCustomers :: Q [Customer] -> Q [Customer]
potentialCustomers cs =
  [ c | c <- cs,
        c_acctbalQ c > avgBalance cs, length (ordersOf c) == 0 ]

countryCodeOf :: Q Customer -> Q Text
countryCodeOf c = subString 1 2 (c_phoneQ c)

livesIn :: Q Customer -> [Text] -> Q Bool
livesIn c countries = countryCodeOf c `elem` toQ countries

q22 :: [Text] -> Q [(Text, Integer, Double)]
q22 countries =
  sortWith (\(view -> (country, _, _)) -> country)
    [ tup3 country (length custs) (sum (map c_acctbalQ custs)) |
      (view -> (country, custs)) <- groupWithKey countryCodeOf pots ]
  where
    pots = potentialCustomers [ c | c <- customers,
                                    c `livesIn` countries ]

minSupplyCost :: Q Integer -> Q Double
minSupplyCost partkey = 
  minimum $ 
  [ ps_supplycostQ ps
  | ps <- partsupps
  , s  <- suppliers
  , n  <- nations
  , r  <- regions
  , partkey == ps_partkeyQ ps
  , s_suppkeyQ s == ps_suppkeyQ ps
  , s_nationkeyQ s == n_nationkeyQ n
  , n_regionkeyQ n == r_regionkeyQ r
  , r_nameQ r == (toQ "EUROPE")
  ]

sortingCriteria
  :: Q (Double, Text, Text, Integer, Text, Text, Text, Text)
  -> Q (Double, Text, Text, Integer)
sortingCriteria (view -> (b, sn, nn, pk, _, _, _, _)) =
  tup4 (b * (toQ $ -1.0)) nn sn pk

q2 :: Q [(Double, Text, Text, Integer, Text, Text, Text, Text)]
q2 = 
  sortWith sortingCriteria $
  [ tup8 (s_acctbalQ s)
           (s_nameQ s)
	   (n_nameQ n)
	   (p_partkeyQ p)
	   (p_mfgrQ p)
	   (s_addressQ s)
	   (s_phoneQ s)
	   (s_commentQ s)
  | p  <- parts
  , ps <- partsupps
  , s  <- suppliers
  , n  <- nations
  , r  <- regions
  , p_partkeyQ p == ps_partkeyQ ps
  , s_suppkeyQ s == ps_suppkeyQ ps
  , p_sizeQ p == (toQ 15)
  , p_typeQ p `like` (toQ "%BRASS")
  , s_nationkeyQ s == n_nationkeyQ n
  , n_regionkeyQ n == r_regionkeyQ r
  , r_nameQ r == (toQ "EUROPE")
  , ps_supplycostQ ps == minSupplyCost (p_partkeyQ p)
  ]

orderQuantity :: Q [LineItem] -> Q Double
orderQuantity lis = sum $ map l_quantityQ lis

jan_q7a :: Q [LineItem]
jan_q7a = snd $ head $ sortWith (orderQuantity . snd) $ groupWithKey l_orderkeyQ lineitems

--------------------------------------------------------------------------------
-- Query written from a database viewpoint

-- List the lineitems of the order with the most parts.
sumPerOrder :: Q [(Integer, Double)]
sumPerOrder = map (\(view -> (ok, lis)) -> pair ok (sum $ map l_quantityQ lis)) 
	      $ groupWithKey l_orderkeyQ lineitems

jan_q7b :: Q [LineItem]
jan_q7b = 
    [ l
    | l <- lineitems
    , (view -> (ok, nrItems)) <- sumPerOrder
    , l_orderkeyQ l == ok
    , nrItems == maximum(map snd sumPerOrder)
    ]

q :: Q [[Integer]]
q = map init (toQ ([] :: [[Integer]]))

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

{-

Being able to write the query using a parallel comprehension would be
nice:

maximum [ t_priceQ t - minPrice
        | t        <- trades'
        | minPrice <- mins $ map t_priceQ trades'
        ]


-}



bestProfit :: Integer -> Integer -> Q Double
bestProfit stock date = 
    maximum [ t_priceQ t - minPrice
            | (view -> (t, minPrice)) <- zip trades' (mins $ map t_priceQ trades')
            ]
  where
    trades' = filter (\t -> t_tidQ t == toQ stock && t_tradeDateQ t == toQ date)
              $ sortWith t_timestampQ trades

hasNationality :: Q Customer -> Text -> Q Bool
hasNationality c nn = 
    or [ n_nameQ n == toQ nn && n_nationkeyQ n == c_nationkeyQ c
       | n <- nations
       ]

ordersWithStatus :: Text -> Q Customer -> Q [Order]
ordersWithStatus status c =
    [ o | o <- ordersOf c, o_orderstatusQ o == toQ status ]

revenue :: Q Order -> Q Double
revenue o = sum [ l_extendedpriceQ l * (1 - l_discountQ l)
                | l <- lineitems
                , l_orderkeyQ l == o_orderkeyQ o
                ]

expectedRevenueFor :: Text -> Q [(Text, [(Integer, Double)])]
expectedRevenueFor nation =
    [ pair (c_nameQ c) [ pair (o_orderdateQ o) (revenue o)
                       | o <- ordersWithStatus "P" c ]
    | c <- customers
    , c `hasNationality` nation
    -- , or [ toQ True | _ <-  ordersWithStatus "P" c ]
    ]

foobar = take 10 $ sortWith id $ map revenue orders

njg3 :: [Integer] -> [Integer] -> [(Integer, Integer)] -> Q [(Integer, Integer)]
njg3 njgxs njgys njgzs =
  [ pair x y
  | x <- toQ njgxs
  , y <- toQ njgys
  , length [ toQ () | z <- toQ njgzs, fst z == x ] > 2
  ]

njgxs1 :: [Integer]
njgxs1 = [1,2]

njgys1 :: [Integer]
njgys1 = [2,3]

njgzs1 :: [(Integer, Integer)]
njgzs1 = [(2, 20), (5, 60), (3, 30)]

backdep5 :: Q [[Integer]]
backdep5 = [ [ x + length xs | x <- take (length xs - 3) xs ] | xs <- toQ ([[1,2,3], [], [4,5,6]] :: [[Integer]]) ]

foo42 :: Q [Integer]
foo42 = filter (const $ toQ True) (toQ ([1,2,3,45] :: [Integer]))

revenue2 :: Integer -> Q [(Integer, Double)]
revenue2 intervalFrom =
    [ pair supplier_no (sum [ ep * (1 - discount)
                            | (view -> (_, ep, discount)) <- g
			    ])
    | (view -> (supplier_no, g)) <- groupWithKey (\(view -> (a, b, c)) -> a) intervalItems
    ]

  where
    intervalItems = [ tup3 (l_suppkeyQ l)
    			   (l_extendedpriceQ l)
			   (l_discountQ l)
		    | l <- lineitems
		    , l_shipdateQ l >= toQ intervalFrom
		    , l_shipdateQ l <= (toQ intervalFrom) + 23
		    ]

q15 :: Integer -> Q [(Integer, (Text, Text, Text, Double))]
q15 intervalFrom = 
    sortWith fst
    [ pair (s_suppkeyQ s)
           (tup4 (s_nameQ s)
	         (s_addressQ s)
	         (s_phoneQ s)
	         total_rev)
    | s <- suppliers
    , (view -> (supplier_no, total_rev)) <- revenue2 intervalFrom
    , s_suppkeyQ s == supplier_no
    , total_rev == (maximum $ map snd $ revenue2 intervalFrom)
    ]

cartprod :: Q ([Integer], [Integer]) -> Q [(Integer, Integer)]
cartprod (view -> (xs, ys)) =
  [ tup2 x y
  | x <- xs
  , y <- ys
  , x == y
  ]

tup :: Q [(Integer, Integer, Integer, Integer)]
tup = map (\(view -> (a, b, c, d)) -> tup4 (a + c) (b - d) b d) (toQ ([(0,0,0,0)] :: [(Integer, Integer, Integer, Integer)]))

frontguard :: Q [[Integer]]
frontguard =
    [ [ y | x > 13, y <- toQ ([1,2,3,4] :: [Integer]), y < 3 ]
    | x <- toQ ([10, 20, 30] :: [Integer])
    ]

njxs1 :: [Integer]
njxs1 = [1,2,3,4,5,6]

njys1 :: [Integer]
njys1 = [3,4,5,6,3,6,4,1,1,1]

nj6 :: [Integer] -> [Integer] -> Q [(Integer, [Integer])]
nj6 njxs njys = 
      [ pair x [ y | y <- toQ njys, x + y > 10, y < 7 ]
      | x <- toQ njxs
      ]
    
main :: IO ()
main = getConn P.>>= \c -> debugQ "q" c (nj6 njxs1 njys1)
-- main = runQX100 x100Conn q P.>>= \r -> putStrLn $ show r
--main = debugQX100 "q" x100Conn q
