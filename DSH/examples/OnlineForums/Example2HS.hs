{-# LANGUAGE QuasiQuotes, OverloadedStrings, TransformListComp #-}

module Main where

-- import qualified Prelude as P

import Spiegel

import qualified Database.DSH as Q
import Database.DSH.Interpreter (fromQ)

import Database.HDBC.PostgreSQL

import System.IO.Unsafe (unsafePerformIO)
import GHC.Exts
import Data.List

conn :: Connection
conn = unsafePerformIO getConnection

threads :: [Thread]
threads = take 10 $ unsafePerformIO $ fromQ conn $ Q.table "spiegelThreads"

posts :: [Post]
posts = unsafePerformIO $ fromQ conn $ Q.table "spiegelPosts"

users :: [User]
users = unsafePerformIO $ fromQ conn $ Q.table "spiegelUsers"

quotes :: [Quote]
quotes = unsafePerformIO $ fromQ conn $ Q.table "spiegelQuotes"

threadsWithRating :: [Thread]
threadsWithRating = [ t | t <- threads, spiegelThreadRating t > 0 ]

postQuotes :: Post -> [Quote]
postQuotes post =
  [ q
  | q <- quotes
  , spiegelPostUrl post == spiegelQuotePostUrl q
  ]

containsQuote :: Post -> Double
containsQuotes post =
  if length (postQuotes post) > 0
      then 1.0
      else 0.0

threadsAndPosts :: [(Thread,[Post])]
threadsAndPosts = 
  [ (the thread, post)
  | thread <- threadsWithRating
  , post   <- posts
  , spiegelThreadUrl thread == spiegelPostThreadUrl post
  , then group by thread
  ]

threadInteractivityAndRatings :: [(Double,Double)]
threadInteractivityAndRatings =
  [ (interactivity , rating)
  | (thread,posts) <- threadsAndPosts
  , let interactivity = sum (map containsQuotes posts) / fromIntegral (length posts)
  , let rating        = spiegelThreadRating thread
  ]

main :: IO ()
main = do
  print (length threads)
  print (length threadsWithRating)
  print (length posts)
  print (length users)
  print (length quotes)

  -- print $ threadInteractivityAndRating