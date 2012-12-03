-- 2c544f140614066b97b9e61030ce7179108e6702
-- optimization string: ESRSRS

{-# LANGUAGE OverloadedStrings, MonadComprehensions, RebindableSyntax, ViewPatterns #-}

module Main where

import qualified Prelude as P
import Database.DSH
import Database.DSH.Flattening
import Database.X100Client

import Records

-- Helper Functions and Queries

t1 :: Q [Integer]
t1 = toQ [1,2,3,4,5]

t2 :: Q [(Integer, Integer)]
t2 = toQ [ (1, 6)
	 , (2, 7)
	 , (3, 8)
	 , (4, 21)
	 , (5, 22)
	 ]

t3 :: Q [(Integer, Integer)]
t3 = toQ [ (6, 42)
         , (7, 43)
	 , (8, 44)
	 , (9, 45)
         ]

q1 :: Q [[[Integer]]]
q1 = [ [ [ v
         | (view -> (b', v)) <- t3
	 , b == b'
	 ]
       | (view -> (a', b)) <- t2
       , a == a'
       ]
     | a <- t1
     ]
  
getConn :: IO X100Info
getConn = P.return $ x100Info "localhost" "48130" Nothing

main :: IO ()
main = getConn 
       P.>>= (\conn -> debugX100VL conn q1)
       P.>>= (\res -> putStrLn $ P.show res)
