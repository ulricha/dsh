{-# LANGUAGE OverloadedStrings, MonadComprehensions, RebindableSyntax, ViewPatterns #-}

module Main where

import qualified Prelude as P
import Database.DSH
import Database.DSH.Flattening
import Database.X100Client

import Records

-- Helper Functions and Queries
  
threadPosts :: Q [(Thread, Post)]
threadPosts =
        [ tuple (thread, post)
        | thread <- threads
        , post   <- posts
        , spiegel_thread_urlQ thread == spiegel_post_thread_urlQ post ]

getConn :: IO X100Info
getConn = P.return $ x100Info "localhost" "48130" Nothing

main :: IO ()
main = getConn 
       -- P.>>= (\conn -> debugX100 conn numberOfDifferentAuthorsThatContributedToEachThread)
       --P.>>= (\conn -> debugX100 conn threadPosts)
       P.>>= (\conn -> debugX100VL conn threadPosts)
       P.>>= (\res -> putStrLn $ P.show res)

{-
main :: IO ()
main = getConn
       P.>>= (\conn -> debugNKLX100 conn threadPosts)
       P.>>= (\res -> putStrLn res)
-}
