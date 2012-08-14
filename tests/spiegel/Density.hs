-- 4b12cf56733af321d77205b9018df23a41cb9ff8
-- optimization string: ERSRSD

{-# LANGUAGE OverloadedStrings, MonadComprehensions, RebindableSyntax, ViewPatterns #-}

module Main where

import qualified Prelude as P
import Database.DSH
import Database.DSH.Flattening
import Database.X100Client

import Records

-- Helper Functions and Queries
  
threadPosts :: Q [(Thread, [Post])]
threadPosts =
  let threadsAndPosts = 
        [ tuple (thread, post)
        | thread <- threads
        , post   <- posts
        , spiegel_thread_urlQ thread == spiegel_post_thread_urlQ post ]
  in
   [ tuple (the ts, ps)
   | postsPerThread <- groupWith (spiegel_thread_urlQ . fst) threadsAndPosts
   , let (view -> (ts, ps)) = unzip postsPerThread ]

-- Determine the density of posts within each thread (number of posts, divided
-- by the time difference between first and last post).

densityOfPostsWithinEachThread :: Q [(Text,Double)]
densityOfPostsWithinEachThread =
  [tuple (spiegel_thread_urlQ thread, density)
      | (view -> (thread, posts)) <- threadPosts
      , let numberOfPosts = integerToDouble (length posts)
      , let postTimes     = map spiegel_post_timeQ posts
      , let firstPostTime = minimum postTimes
      , let lastPostTime  = maximum postTimes
      , (lastPostTime - firstPostTime) > 0
      , let density       = numberOfPosts / (lastPostTime - firstPostTime)
  ]

getConn :: IO X100Info
getConn = P.return $ x100Info "localhost" "48130" Nothing

main :: IO ()
main = getConn 
       P.>>= (\conn -> debugX100VL conn densityOfPostsWithinEachThread)
       P.>>= (\res -> putStrLn $ P.show res)
