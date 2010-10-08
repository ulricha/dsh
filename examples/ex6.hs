{-# LANGUAGE QuasiQuotes, OverloadedStrings #-}

module Main where

-- import qualified Prelude as P

import Spiegel

import Prelude ()
import qualified Prelude as P

import Ferry
-- import Ferry.Interpreter (fromQ)
import Ferry.HSCompiler (fromQ)

import Database.HDBC.PostgreSQL

-- import System.IO.Unsafe (unsafePerformIO)
-- import GHC.Exts
-- import Data.List

threads :: Q [Thread]
threads = table "spiegelThreads"

posts :: Q [Post]
posts = table "spiegelPosts"

-- users :: Q [User]
-- users = table "spiegelUsers"

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
  
  fromQ conn (length threads) P.>>= P.print
  fromQ conn (length posts)   P.>>= P.print
  fromQ conn (length quotes)  P.>>= P.print

  fromQ conn (threadInteractivityAndRatings) P.>>= P.print