{-# LANGUAGE QuasiQuotes, OverloadedStrings #-}

module Main where

-- import qualified Prelude as P

import Records

import Prelude ()
import qualified Prelude as P

import Database.DSH
import Database.DSH.Compiler (fromQ)

import Database.HDBC.PostgreSQL

import Math.Statistics
-- import Graphics.Gnuplot.Simple

import System.Cmd
import qualified Data.List as L

threads :: Q [Thread]
threads = tableWithKeys "spiegelThreads" [["spiegelThreadUrl"]]

posts :: Q [Post]
posts = tableWithKeys "spiegelPosts" [["spiegelPostUrl"]]

quotes :: Q [Quote]
quotes = table "spiegelQuotes"

threadsWithRating :: Q [Thread]
threadsWithRating =
  [$qc| t
      | t <- threads
      , (spiegelThreadRatingQ t) > 0
  |]

postQuotes :: Q Post -> Q [Quote]
postQuotes post =
  [$qc| q
      | q <- quotes
      , spiegelPostUrlQ post == spiegelQuotePostUrlQ q
  |]

containsQuotes :: Q Post -> Q Double
containsQuotes post =
  (length (postQuotes post) > 0) ? (1,0)

threadsAndPosts :: Q [ (Thread , [Post]) ]
threadsAndPosts = 
  [$qc| fromView (the thread, post)
      | thread <- threadsWithRating
      , post   <- posts
      , spiegelThreadUrlQ thread == spiegelPostThreadUrlQ post
      , then group by thread
  |]

threadInteractivityAndRatings :: Q [(Double,Double)]
threadInteractivityAndRatings =
  [$qc| fromView (interactivity , rating)
      | (thread,posts) <- threadsAndPosts
      , let interactivity = sum (map containsQuotes posts) P./ integerToDouble (length posts)
      , let rating        = spiegelThreadRatingQ thread
  |]

main :: IO ()
main = do
  conn <- getConnection
  
  irs <- fromQ conn (threadInteractivityAndRatings)
  
  P.putStr "Pearson Correlation = "
  P.print ((P.uncurry pearson) (P.unzip (L.sort irs)))
  
  -- plotPath [] (L.sort irs)
  
  P.return ()
  
  