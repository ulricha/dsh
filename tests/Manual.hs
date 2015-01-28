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
{-# LANGUAGE FlexibleContexts      #-}

module Main where


import qualified Prelude as P
import Database.DSH
import Database.DSH.Compiler

-- import Database.X100Client

import Database.HDBC.PostgreSQL

-- import qualified Data.Text as T

-- import TPCH

-- data Foo = Foo { foo1 :: Integer, foo2 :: Text, foo3 :: Integer }

-- deriveDSH ''Foo
-- deriveTA ''Foo
-- generateTableSelectors ''Foo

getConn :: IO Connection
getConn = connectPostgreSQL "user = 'au' password = 'foobar' host = 'localhost' port = '5432' dbname = 'trades'"

-- x100Conn :: X100Info
-- x100Conn = x100Info "localhost" "48130" Nothing

-- xs :: Q [(Text, [Integer])]
-- xs = toQ [("a", [10, 20]), ("b", [30, 40])]

-- q :: Q [[Integer]]
-- q = map snd xs

-- q1 :: Q [[Integer]]
-- q1 = [ nub [ l_partkeyQ l | l <- lineitems, l_orderkeyQ l == o_orderkeyQ o ]
--      | o <- orders
--      ]

-- q2 :: Q [Bool]
-- q2 = [ and [ l_commitdateQ l > o_orderdateQ o | l <- lineitems, l_orderkeyQ l == o_orderkeyQ o ]
--      | o <- orders
--      ]

-- q21 :: Q [(Bool,[Integer])]
-- q21 = [ pair (and [ l_commitdateQ l > o_orderdateQ o | l <- lineitems, l_orderkeyQ l == o_orderkeyQ o ])
--              (nub [ l_partkeyQ l | l <- lineitems, l_orderkeyQ l == o_orderkeyQ o ])
--      | o <- orders
--      ]

data Trade = Trade
    { t_amount    :: Double
    , t_price     :: Double
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

mins :: (Ord a, QA a, TA a) => Q [a] -> Q [a]
mins xs = [ minimum [ y | (view -> (y,j)) <- number xs, j <= i ] 
          | (view -> (x,i)) <- number xs
          ]

margins :: (Ord a, Num (Q a), QA a, TA a) => Q [a] -> Q [a]
margins xs = [ x - y | (view -> (x,y)) <- zip xs (mins xs) ]

profit :: (Ord a, Num (Q a), QA a, TA a) => Q [a] -> Q a
profit xs = maximum (margins xs)

bestProfit :: Integer -> Integer -> Q [Trade] -> Q Double
bestProfit stock date trades =
    profit [ t_priceQ t * t_amountQ t
           | t <- sortWith t_timestampQ trades
           , t_tidQ t == toQ stock
           , t_tradeDateQ t == toQ date
           ]

---

totalPrice :: Q Trade -> Q Double
totalPrice t = t_priceQ t * t_amountQ t

mins' :: Q [Trade] -> Q [Double]
mins' xs = [ minimum [ totalPrice t'  | (view -> (t',j)) <- number xs, j <= i ] 
          | (view -> (_,i)) <- number xs
          ]

margins' :: Q [Trade] -> Q [Double]
margins' ts = [ totalPrice t - m | (view -> (t,m)) <- zip ts (mins' ts) ]

profit' :: Q [Trade] -> Q Double
profit' ts = maximum (margins' ts)

bestProfit' :: Integer -> Integer -> Q [Trade] -> Q Double
bestProfit' stock date trades =
    profit' [ t
            | t <- sortWith t_timestampQ trades
            , t_tidQ t == toQ stock
            , t_tradeDateQ t == toQ date
            ]
           
main :: IO ()
main = getConn P.>>= \c -> debugQ "q" c (bestProfit' 23 42 trades)  P.>>= \r -> putStrLn (show r)
-- main = runQX100 x100Conn q P.>>= \r -> putStrLn $ show r
--main = debugQX100 "q" x100Conn q
