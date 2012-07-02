{-# LANGUAGE OverloadedStrings, MonadComprehensions, RebindableSyntax #-}

module Main where

import Prelude()
import Database.DSH

import Records

import qualified Data.Text as T
import qualified Data.List as L

-- Helper Functions and Queries
  
threadPosts :: Q [(Thread, [Post])]
threadPosts =
  let threadsAndPosts = 
        [ (thread, post)
        | thread <- threads
        , post   <- posts
        , spiegel_thread_urlQ thread == spiegel_post_thread_urlQ post ]
  in
   [ (the threads, posts)
   | postsPerThread <- groupWith (spiegel_thread_urlQ . fst) threadsAndPosts
   , let (threads, posts) = unzip postsPerThread ]

postQuotes :: Q [(Post, [Quote])]
postQuotes =
  let postsAndQuotes =
        [ (post, quote)
        | post  <- posts
        , quote <- quotes
        , spiegel_post_urlQ post == spiegel_quote_urlQ quote ]
  in 
   [ (the posts, quotes)
   | quotesPerPost <- groupWith (spiegel_post_urlQ . fst) postsAndQuotes
   , let (posts, quotes) = unzip quotesPerPost ]

-- Given a post url retuns Just post creation time
-- or Nothing if there is no such post
postTime :: Q Text -> Q (Maybe Double)
postTime url = listToMaybe
  [spiegel_post_timeQ post
      | post  <- posts
      , spiegel_post_urlQ post == url
  ]

-- The remaining queries are from simple.pdf

-- This query is more accurate than values given in the spiegel_thread_replies
-- column of spiegel_threads table by capturing the posts that were written during
-- the extration process
numberOfPostsWithinEachThread :: Q [(Text,Integer)]
numberOfPostsWithinEachThread =
  [ tuple (spiegel_thread_urlQ thread, length posts)
      | (thread,posts) <- threadPosts
  ]

-- Content lengths are calculated outside the database
lengthOfEachPost :: Q [(Text,Text)]
lengthOfEachPost =
  [ tuple (spiegel_post_urlQ p, spiegel_post_contentQ p)
      | p <- posts
  ]

numberOfDifferentAuthorsThatContributedToEachThread :: Q [(Text,Integer)]
numberOfDifferentAuthorsThatContributedToEachThread = 
  [ tuple (spiegel_thread_urlQ thread, length (nub userUrls))
      | (thread,posts) <- threadPosts
      , let userUrls = map spiegel_post_user_urlQ posts
  ]

-- Determine the density of posts within each thread (number of posts, divided
-- by the time difference between first and last post).

densityOfPostsWithinEachThread :: Q [(Text,Double)]
densityOfPostsWithinEachThread =
  [tuple (spiegel_thread_urlQ thread, density)
      | (thread,posts) <- threadPosts
      , let numberOfPosts = integerToDouble (length posts)
      , let postTimes     = map spiegel_post_timeQ posts
      , let firstPostTime = minimum postTimes
      , let lastPostTime  = maximum postTimes
      , (lastPostTime - firstPostTime) > 0
      , let density       = numberOfPosts / (lastPostTime - firstPostTime)
  ]

numberOfQuotesForEachPost :: Q [(Text,Integer)]
numberOfQuotesForEachPost =
  [ tuple (spiegel_post_urlQ post, length quotes)
      | (post,quotes) <- postQuotes
  ]

durationBetweenPostAndFirstQuotation :: Q [(Text,Double)]
durationBetweenPostAndFirstQuotation = 
  [ tuple (spiegel_post_urlQ post, duration)
      | (post,quotes) <- postQuotes
      , let quotingPostUrls = map spiegel_quote_post_urlQ quotes
      , let quotingPostTimes = mapMaybe postTime quotingPostUrls
      , let firstQuoteTime = minimum quotingPostTimes
      , let duration = firstQuoteTime - spiegel_post_timeQ post
  ]

avarageDurationBetweenPostAndFirstQuotation :: Q [Double]
avarageDurationBetweenPostAndFirstQuotation = 
  [ sum durations / integerToDouble (length durations)
      | let durations = map snd durationBetweenPostAndFirstQuotation
 ]

{-
numberOfQuotesReceivedByEachAuthor :: Q [(Text,Integer)]
numberOfQuotesReceivedByEachAuthor =
  [ tuple (the postAuthor, sum quoteNumber)
      | (post,quotes) <- postQuotes
      , let quoteNumber = length quotes
      , let postAuthor = spiegel_post_user_urlQ post
      , then group by postAuthor
  ]
-}

main :: IO ()
main = do
  runQ numberOfPostsWithinEachThread
    >>= csvExport "numberOfPostsWithinEachThread.csv"
  runQ numberOfDifferentAuthorsThatContributedToEachThread
    >>= csvExport "numberOfDifferentAuthorsThatContributedToEachThread.csv"
  runQ densityOfPostsWithinEachThread
    >>= csvExport "densityOfPostsWithinEachThread.csv"
  runQ numberOfQuotesForEachPost
    >>= csvExport "numberOfQuotesForEachPost.csv"
  runQ durationBetweenPostAndFirstQuotation
    >>= csvExport "durationBetweenPostAndFirstQuotation.csv"
  runQ avarageDurationBetweenPostAndFirstQuotation
    >>= csvExport "avarageDurationBetweenPostAndFirstQuotation.csv"
  runQ numberOfQuotesReceivedByEachAuthor
    >>= csvExport "numberOfQuotesReceivedByEachAuthor.csv"

  r <- runQ lengthOfEachPost
  let f :: [(Text,Text)] -> [(Text,Integer)]
      f = L.map (\(u,c) -> (u,fromIntegral (T.length c)))
  csvExport "lengthOfEachPost.csv" (f r)
