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

-- | A number of more complex DSH examples based on the TPC-H
-- benchmark schema. A data generator is available at
-- <http://www.tpc.org/tpch/>. Note that DSH currently does not
-- support temporal and decimal types. Those have to be mapped to
-- epoch integers and doubles, respectively. The script
-- 'examples/dshify-tpch.sql' modifies a PostgreSQL TPCH database
-- accordingly.
module Main where

import qualified Prelude as P
import Database.DSH
import Database.DSH.Compiler

import Database.HDBC.PostgreSQL

-- | We declare a flat record type that maps to the relational
-- schema. Names of record selectors should match attribute names in
-- the schema. Note that record selectors should be listed in
-- alphabetical order.
data LineItem = LineItem
    { l_comment       :: Text
    , l_commitdate    :: Integer
    , l_discount      :: Double
    , l_extendedprice :: Double
    , l_linenumber    :: Integer
    , l_linestatus    :: Text
    , l_orderkey      :: Integer
    , l_partkey       :: Integer
    , l_quantity      :: Double
    , l_receiptdate   :: Integer
    , l_returnflag    :: Text
    , l_shipdate      :: Integer
    , l_shipinstruct  :: Text
    , l_shipmode      :: Text
    , l_suppkey       :: Integer
    , l_tax           :: Double
    }
    deriving (Show)

-- A bit of Template Haskell code automatically derives instances and
-- infrastructure to use the record type in DSH queries. For each
-- record selector, we derive a variant that can be used in
-- queries. For example, we get a lifted record selector 
-- 'l_commentQ :: Q LineItem -> Q Text'.
deriveDSH ''LineItem
deriveTA ''LineItem
generateTableSelectors ''LineItem

-- | The 'table' combinator implements a database table scan.
lineitems :: Q [LineItem]
lineitems = table "lineitem" $ TableHints [Key ["l_orderkey", "l_linenumber"]] NonEmpty

data Order = Order
    { o_clerk         :: Text
    , o_comment       :: Text
    , o_custkey       :: Integer
    , o_orderdate     :: Integer
    , o_orderkey      :: Integer
    , o_orderpriority :: Text
    , o_orderstatus   :: Text
    , o_shippriority  :: Integer
    , o_totalprice    :: Double
    }
    deriving (Show)

deriveDSH ''Order
deriveTA ''Order
generateTableSelectors ''Order

orders :: Q [Order]
orders = table "orders" $ TableHints [Key ["o_orderkey"]] NonEmpty

--------------------------------------------------------------------------------

-- Select all lineitems that were shipped before a given date
ordersBefore :: Q Integer -> Q [LineItem]
ordersBefore date = [ li | li <- lineitems , l_shipdateQ li <= date ]

fst9 :: (QA a, QA b, QA c, QA d, QA e, QA f, QA g, QA h, QA i) => Q (a, b, c, d, e, f, g, h, i) -> Q a
fst9 (view -> (a, _, _, _, _, _, _, _, _)) = a

-- Compute the revenue of a single lineitem
revenue :: Q LineItem -> Q Double
revenue li = l_extendedpriceQ li * (1 - l_discountQ li)

-- TPC-H benchmark query Q1
q1 :: Q Integer 
   -> Q [((Text, Text), Double, Double, Double, Double, Double, Double, Double, Integer)]
q1 maxDate = sortWith fst9 $ 
     [ tup9
	  k
	  (sum $ map l_quantityQ lis)
	  (sum $ map l_extendedpriceQ lis)
	  (sum $ map revenue lis)
	  (sum $ map (\li -> revenue li * (1 + l_taxQ li)) lis)
	  (avg $ map l_quantityQ lis)
	  (avg $ map l_extendedpriceQ lis)
	  (avg $ map l_discountQ lis)
	  (length lis)
      | (view -> (k, lis)) <- groupWithKey (\li -> pair (l_returnflagQ li) (l_linestatusQ li)) 
                              $ ordersBefore maxDate
      ]

--------------------------------------------------------------------------------

data Range = Range { start :: Integer, end :: Integer }

inside :: Q Integer -> Range -> Q Bool
inside d range = d >= toQ (start range) && d < toQ (end range)

lineItemsOf :: Q Order -> Q [LineItem]
lineItemsOf o = [ l | l <- lineitems,
                      l_orderkeyQ l == o_orderkeyQ o ]

-- Has at least one of the orders' items been delivered late?
hasLateItem :: Q Order -> Q Bool
hasLateItem o =
  or [ l_commitdateQ l < l_receiptdateQ l | l <- lineItemsOf o ]

-- Compute the number of delayed orders per priority level in the
-- given quarter (TPC-H benchmark query Q4).
q4 :: Range -> Q [(Text, Integer)]
q4 quarter = sortWith fst
  [ pair priority (length delays)
  | (view -> (priority, delays)) <- groupWithKey o_orderpriorityQ delayedOrders ]
  where
    delayedOrders = [ o | o <- orders
                    , o_orderdateQ o `inside` quarter
                    , hasLateItem o
                    ]

--------------------------------------------------------------------------------

getConn :: IO Connection
getConn = connectPostgreSQL "user = 'au' password = 'foobar' host = 'localhost' dbname = 'tpchsmall'"

execQ :: (Show a,QA a) => Q a -> IO ()
execQ q = getConn P.>>= \conn -> (runQ conn q P.>>= P.print) P.>> disconnect conn

main :: IO ()
main = sequence_  [ execQ $ q1 904663977
                  -- Compute Q4 for a three-month interval
                  , execQ (q4 $ Range 741540777 749489577)
                  ]
