{-# LANGUAGE QuasiQuotes, OverloadedStrings #-}

module Main where

import Records

import Prelude ()
import qualified Prelude as P

import Database.DSH
import Database.DSH.Compiler (fromQ)

import Math.Statistics
import qualified Data.List as L

threads :: Q [Thread]
-- threads = table "spiegelThreads"
threads = tableWithKeys "spiegelThreads" [["spiegelThreadUrl"]]

posts :: Q [Post]
-- posts = table "spiegelPosts"
posts = tableWithKeys "spiegelPosts" [["spiegelPostUrl"]]

quotes :: Q [Quote]
quotes = table "spiegelQuotes"

threadsWithRating =
  [$qc| t
      | t <- threads
      , (spiegelThreadRatingQ t) > 0
  |]

postQuotes post =
  [$qc| q
      | q <- quotes
      , spiegelPostUrlQ post == spiegelQuotePostUrlQ q
  |]

containsQuotes post =
  (length (postQuotes post) > 0) ? (1,0)

threadsAndPosts = 
  [$qc| fromView (the thread, post)
      | thread <- threadsWithRating
      , post   <- posts
      , spiegelThreadUrlQ thread == spiegelPostThreadUrlQ post
      , then group by (spiegelThreadUrlQ thread) -- thread
  |]

threadInteractivityAndRatings =
  [$qc| fromView (interactivity , rating)
      | (thread,posts) <- threadsAndPosts
      , let interactivity = sum (map containsQuotes posts) / integerToDouble (length posts)
      , let rating        = spiegelThreadRatingQ thread
  |]

main = do
  conn <- getConnection
  
  irs <- fromQ conn (threadInteractivityAndRatings)
  
  P.putStr "Correlation Coefficient = "
  P.print ((P.uncurry pearson) (P.unzip (L.sort irs)))
  
  -- plotPath [] (L.sort irs)
  
  P.return ()