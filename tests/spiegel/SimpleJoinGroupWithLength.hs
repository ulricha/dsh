-- 7b57bb2a8c4bcb877f1b32c049d73a54a3c8be54
-- optimization string: ERSRSD

{-# LANGUAGE OverloadedStrings, MonadComprehensions, RebindableSyntax, ViewPatterns #-}

module Main where

import qualified Prelude as P
import Database.DSH
import Database.DSH.Flattening
import Database.X100Client

import Records

threadPosts :: Q [(Text, Integer)]
threadPosts =
  let threadsAndPosts = 
        [ tuple (thread, post)
        | thread <- threads
        , post   <- posts
        , spiegel_thread_urlQ thread == spiegel_post_thread_urlQ post ]
  in
   [ tuple (spiegel_thread_urlQ (the ts), length ps)
   | postsPerThread <- groupWith (spiegel_thread_urlQ . fst) threadsAndPosts
   , let (view -> (ts, ps)) = unzip postsPerThread ]


getConn :: IO X100Info
getConn = P.return $ x100Info "localhost" "48130" Nothing

main :: IO ()
main = getConn 
       P.>>= (\conn -> debugX100VL conn threadPosts)
       P.>>= (\res -> putStrLn $ P.show res)
