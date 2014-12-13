{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE RebindableSyntax    #-}
{-# LANGUAGE ViewPatterns        #-}

-- | Some simple example queries over (literal) integer lists.
module Main where

import qualified Prelude as P
import Database.DSH
import Database.DSH.Compiler

import Database.HDBC.PostgreSQL

-- The 'toQ' combinator constructs a query that returns a given native
-- Haskell value.
ints :: Q [Integer]
ints = toQ [1 .. 10]

ints2 :: Q [Integer]
ints2 = toQ $ [1..3] P.++ [7..12]

-- Comprehensions are the main way to express queries
query1 :: Q [(Integer,Integer)]
query1 =  [ pair i1 i2
          | i1 <- ints
          , i2 <- ints2
          , i1 == i2
          ]

-- Pattern matching on tuples is supported using View Patterns.
query2 :: Q [(Integer,Integer)]
query2 =  [ pair i1 i2
          | (view -> (i1,i2)) <- query1
          , i1 > 3
          ]

-- List combinators can be used freely.
query3 :: Q [(Integer, Integer)]
query3 = zip (drop 1 ints) ints

-- Existential quantification
query4 :: Q [Integer]
query4 = [ x | x <- ints, x `elem` ints2 ]

-- Existential quantification expressed using a boolean aggregate.
query5 :: Q [Integer]
query5 = [ x | x <- ints, or [ x == y | y <- ints2 ] ]

-- Existential and universal quantification
query6 :: Q [Integer]
query6 = [ x | x <- ints, or [ x == y | y <- ints2 ] ]
         ++
         [ x | x <- ints, and [ not $ x == y | y <- ints2 ] ]

-- Query results may be nested.
query7 :: Q [[Integer]]
query7 = [ [ y | y <- ints, y < x ] | x <- ints2 ] 

-- Sorting
query8 :: Q [(Integer, Integer)]       
query8 = take 3 $ sortWith fst $ toQ [(3,4),(5,1),(9,12),(8,3),(6,15)]

xys :: Q [(Integer, Integer)]
xys = toQ [(3,5),(4,5),(3,8),(3,9),(5,6),(4,0)]

-- Grouping and aggregation
query9 :: Q [(Integer, Integer)]
query9 = [ pair k (sum [ snd ge | ge <- g ])
         | (view -> (k, g)) <- groupWithKey (\xy -> fst xy)  xys
         ]

-- To execute queries, a HDBC connection to a PostgreSQL database must
-- be supplied.
getConn :: IO Connection
getConn = connectPostgreSQL "user = 'au' password = 'foobar' host = 'localhost' dbname = 'test'"

-- Given a connection, queries are executed using the 'runQ'
-- combinator.
execQ :: (Show a,QA a) => Q a -> IO ()
execQ q = getConn P.>>= \conn -> (runQ conn q P.>>= P.print) P.>> disconnect conn

main :: IO ()
main = execQ ints 
       P.>> execQ query1 
       P.>> execQ query2 
       P.>> execQ query3
       P.>> execQ query4
       P.>> execQ query5
       P.>> execQ query6
       P.>> execQ query7
       P.>> execQ query8
       P.>> execQ query9
