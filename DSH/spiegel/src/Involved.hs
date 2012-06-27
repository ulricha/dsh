{-# LANGUAGE QuasiQuotes, OverloadedStrings #-}

module Main where

import Prelude()
import Database.DSH

import Records

-- Helper Functions and Queries

-- | Post (if any) which gets quoted
quotedPost :: Q Quote -> Q (Maybe Post)
quotedPost quote = listToMaybe
  [$qc| post
      | post <- posts
      , spiegel_post_urlQ post == spiegel_quote_urlQ quote
  |]

-- | Post which contains the current quote
quotePost :: Q Quote -> Q Post
quotePost quote = the
  [$qc| p
      | p <- posts
      , spiegel_quote_post_urlQ quote == spiegel_post_urlQ p
  |]

postUser :: Q Post -> Q User
postUser post = the
  [$qc| user
      | user <- users
      , spiegel_user_urlQ user == spiegel_post_user_urlQ post
  |]

quotedUser :: Q Quote -> Q (Maybe User)
quotedUser quote = listToMaybe
  [$qc| user
      | user <- users
      , post <- posts
      , spiegel_post_urlQ post == spiegel_quote_urlQ quote
      , spiegel_user_urlQ user == spiegel_post_user_urlQ post
  |]


-- | Get all quotes of the current post
postQuotes :: Q Post -> Q [Quote]
postQuotes post =
  [$qc| q
      | q <- quotes
      , spiegel_post_urlQ post == spiegel_quote_post_urlQ q
  |]

-- | Get all posts which quote the current post
quotingPosts :: Q Post -> Q [Post]
quotingPosts post =
  [$qc| quotePost q
      | q <- quotes
      , spiegel_post_urlQ post == spiegel_quote_urlQ q
  |]

threadPosts :: Q Thread -> Q [Post]
threadPosts thread =
  [$qc| p
      | p <- posts
      , spiegel_thread_urlQ thread == spiegel_post_thread_urlQ p
  |]

threadsWithRating :: Q [Thread]
threadsWithRating =
  [$qc| t | t <- threads , spiegel_thread_ratingQ t > 0  |]

threadsAndPosts :: Q [(Thread,[Post])]
threadsAndPosts =
  [$qc| tuple (the thread, post)
      | thread <- threadsWithRating
      , post   <- posts
      , spiegel_thread_urlQ thread == spiegel_post_thread_urlQ post
      , then group by thread
  |]

-- 1.1 "Simple relation between interactivity and rating" query from involved.pdf

containsQuotes :: Q Post -> Q Double
containsQuotes post = (length (postQuotes post) > 0) ? (1,0)

threadInteractivityAndRatings :: Q [(Double,Double)]
threadInteractivityAndRatings =
  [$qc| tuple (interactivity, rating)
      | (thread,posts) <- threadsAndPosts
      , let interactivity = sum (map containsQuotes posts) / integerToDouble (length posts)
      , let rating        = spiegel_thread_ratingQ thread
  |]

-- 1.2 "Complex relation between interactivity, author role, and rating" from Involved.pdf

userExperience :: Q User -> Q Integer
userExperience user = spiegel_user_roleQ user == "Erfahrener Benutzer" ? (1,0)

threadInteractivityExperienceAndRatings :: Q [(Double,Double,Double)]
threadInteractivityExperienceAndRatings =
  [$qc| tuple (interactivity, interactivityExperience, rating)
      | (thread,posts) <- threadsAndPosts
      , let interactivity = sum (map containsQuotes posts) / integerToDouble (length posts)
      , let quotes = concatMap postQuotes posts
      , let quoteNumber = length quotes
      , quoteNumber > 0
      , let experience = sum (map userExperience (mapMaybe quotedUser quotes))
      , let interactivityExperience = integerToDouble experience / integerToDouble quoteNumber
      , let rating = spiegel_thread_ratingQ thread
  |]

-- 2.1 "time until quoted"

timeUntilQuotedWithPosturlAndTimediff :: Q [(Text, Double)]
timeUntilQuotedWithPosturlAndTimediff =
  [$qc| tuple (spiegel_post_urlQ p, t)
      | p <- posts
      , spiegel_user_nameQ (postUser p) /= "sysop"
      , q <- quotingPosts p
      , let t = spiegel_post_timeQ q - spiegel_post_timeQ p
  |]

averageTimeUntilQuoted :: Q Double
averageTimeUntilQuoted =
  let numOfQuotes = length timeUntilQuotedWithPosturlAndTimediff
      totaleTime  = sum $ map snd timeUntilQuotedWithPosturlAndTimediff
      average     = totaleTime / integerToDouble numOfQuotes
   in average

-- 2.2 Relative post position and its influence on quoting probability

-- TODO: This task requires a "postcount=.." field in the post url, which is
-- currently missing in the database

-- 3.1 Quoting probability based on user category

numberOfPosts :: Q Text     -- ^ user url
              -> Q Integer
numberOfPosts u_url =
  length . filter (u_url ==) $ map spiegel_post_user_urlQ posts

userRole :: Q Text            -- ^ user url
         -> Q Text
userRole u_url =
  spiegel_user_roleQ . the $ filter ((u_url ==) . spiegel_user_urlQ) users

quotingProbabilityBasedOnUserCategory :: Q [(Text, Text, Double)]
quotingProbabilityBasedOnUserCategory =
  [$qc| tuple (u_url, role, probability)
      | qps <- groupWith id
             . map spiegel_post_user_urlQ
             . nub
             . mapMaybe quotedPost
             $ quotes
      , let u_url       = head qps
      , let quoteCount  = length qps
      , let postCount   = numberOfPosts u_url
      , let probability = itd quoteCount / itd postCount
      , let role        = userRole u_url
  |]
  where itd = integerToDouble

main :: IO ()
main = do

  putStrLn "running: 1.1 - threadInteractivityAndRatings\n\
           \output:  threadInteractivityAndRatings.csv"
  runQ threadInteractivityAndRatings
    >>= csvExport "threadInteractivityAndRatings.csv"

  putStrLn "running: 1.2 - threadInteractivityExperienceAndRatings\n\
           \output:  threadInteractivityExperienceAndRatings.csv"
  runQ threadInteractivityExperienceAndRatings
    >>= csvExport "threadInteractivityExperienceAndRatings.csv"

  putStrLn "running: 2.1 - timeUntilQuotedWithPosturlAndTimediff\n\
           \output:  timeUntilQuotedWithPosturlAndTimediff.csv"
  runQ timeUntilQuotedWithPosturlAndTimediff
    >>= csvExport "timeUntilQuotedWithPosturlAndTimediff.csv"

  putStrLn "running: 2.1 - averageTimeUntilQuoted\n\
           \output:  averageTimeUntilQuoted.txt"
  runQ averageTimeUntilQuoted
    >>= writeFile "averageTimeUntilQuoted.txt" . (++"\n") . show

  -- 2.2 missing

  putStrLn "running: 3.1 - quotingProbabilityBasedOnUserCategory\n\
           \output   quotingProbabilityBasedOnUserCategory.csv"
  runQ quotingProbabilityBasedOnUserCategory
    >>= csvExport "quotingProbabilityBasedOnUserCategory.csv"
