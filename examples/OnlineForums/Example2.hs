{-# LANGUAGE QuasiQuotes, OverloadedStrings #-}

module Main where

import Records

import Prelude ()
import qualified Prelude as P

import Database.DSH
import Database.DSH.Compiler (fromQ,debugFromQ)

import Math.Statistics
import qualified Data.List as L



-- Relation between interactivity and rating
-- 
-- For instance, when readers rate a thread positively, they could do it because
-- of the topic (it’s a fascinating or important topic), but they could also do
-- it because of the quality of the discussion itself. A potential marker of a
-- good discussion quality is the interactivity. Thus, the first step of the
-- query should compute an interactivity variable for each thread, defined as the
-- percentage of posts in the thread that contain quotes.
-- 
-- To get this, one would have to check for each post [spiegelPostUrl] in a given
-- thread [spiegelPostThreadUrl] whether it contains a quote
-- [spiegelQuotePostUrl] or not (coded binary), sum up the binary values over the
-- entire thread, and divide it by the number of posts in the thread
-- [spiegelThreadReplies]. The interactivity variable would be named
-- [spiegelThreadInteractivity] and saved as new variable in the thread database.
-- 
-- For the analysis of this research question we would further have to
-- exclude all threads that did not receive a rating [spiegelThreadRating].
-- 
-- Finally, we would need a Pearson correlation coefficient (plus significance).
-- This would allow us to see whether interactivity [spiegelThreadInteractivity]
-- is positively correlated with the average rating of the thread
-- [spiegelThreadRating].

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
  
  irs <- debugFromQ conn (threadInteractivityAndRatings)
  
  P.putStr "Correlation Coefficient = "
  P.print ((P.uncurry pearson) (P.unzip (L.sort irs)))
  
  -- plotPath [] (L.sort irs)
  
  P.return ()