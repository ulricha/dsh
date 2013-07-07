{-# LANGUAGE RebindableSyntax    #-}
{-# LANGUAGE ViewPatterns        #-}
{-# LANGUAGE MonadComprehensions #-}
    
-- | This module contains testcases for monad comprehensions. We store them in a
-- separate module because they rely on RebindableSyntax and hidden Prelude.
   
module ComprehensionTests where

import qualified Prelude as P
import Database.DSH
       
---------------------------------------------------------------
-- Comprehensions for quickcheck tests

eqjoin :: Q ([Integer], [Integer]) -> Q [(Integer, Integer)]
eqjoin (view -> (xs, ys)) = 
  [ tuple2 x y
  | x <- xs
  , y <- ys
  , x == y
  ]

  
eqjoinproj :: Q ([Integer], [Integer]) -> Q [(Integer, Integer)]
eqjoinproj (view -> (xs, ys)) = 
  [ tuple2 x y
  | x <- xs
  , y <- ys
  , (2 * x) == y
  ]

eqjoinpred :: Q (Integer, [Integer], [Integer]) -> Q [(Integer, Integer)]
eqjoinpred (view -> (x', xs, ys)) = 
  [ tuple2 x y
  | x <- xs
  , y <- ys
  , x == y
  , x > x'
  ]

eqjoin3 :: Q ([Integer], [Integer], [Integer]) -> Q [(Integer, Integer, Integer)]
eqjoin3 (view -> (xs, ys, zs)) = 
  [ tuple3 x y z
  | x <- xs
  , y <- ys
  , z <- zs
  , x == y
  , y == z
  ]
  
eqjoin_nested :: Q ([(Integer, [Integer])], [Integer]) -> Q [((Integer, [Integer]), Integer)]
eqjoin_nested args =
  [ pair x y
  | x <- fst args
  , y <- snd args
  , fst x == y
  ]

nestjoin :: Q ([Integer], [Integer]) -> Q [(Integer, [Integer])]
nestjoin (view -> (xs, ys)) =
  [ tuple2 x [ y | y <- ys, x == y]
  | x <- xs
  ]
  
--------------------------------------------------------------
-- Comprehensions for HUnit tests

eqjoin_nested1 :: Q [((Integer, [Char]), Integer)]
eqjoin_nested1 =
    [ pair x y
    | x <- (toQ ([(10, ['a']), (20, ['b']), (30, ['c', 'd']), (40, [])] :: [(Integer, [Char])]))
    , y <- (toQ [20, 30, 30, 40, 50])
    , fst x == y
    ]
