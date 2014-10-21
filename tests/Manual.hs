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
    
main :: IO ()
-- main = getConn P.>>= \c -> debugQ "q" c $ qj3 $ toQ (([], [], []) :: ([Integer], [Integer], [Integer]))
-- main = getConn P.>>= \c -> debugQ "q" c foo
main = getConn P.>>= \c -> debugQ "q" c $ q22 (P.map T.pack ["foo", "bar"])
--main = debugQX100 "q" x100Conn $ q (toQ [1..50])
--main = debugQX100 "q1" x100Conn q1
