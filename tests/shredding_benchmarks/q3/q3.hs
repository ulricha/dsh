-- 5843fced1434caa619b3e12b83dc964547a703d1
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

t4 :: Q [(Integer, Integer)]
t4 = toQ [ (21, 110)
	 , (22, 111)
	 ]

nested2 :: Q [[[Integer]]]
nested2 = [ [ [ v
              | (view -> (b', v)) <- t3
	      , b' == b
              ]
            | (view -> (a', b)) <- t2
	    , a == a'
	    ]
	  | a <- t1 
	  ]
	  ++
          [ [ [ v
              | (view -> (b', v)) <- t4
	      , b' == b
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
       P.>>= (\conn -> debugX100VL conn nested2)
       P.>>= (\res -> putStrLn $ P.show res)
