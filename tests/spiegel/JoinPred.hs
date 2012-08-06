-- 08d09ddf93cefba810e83a48fff3ca0b4f1839ce
-- optimization string: EPCRSCRCRSD
{-# LANGUAGE OverloadedStrings, MonadComprehensions, RebindableSyntax, ViewPatterns #-}

module Main where

import qualified Prelude as P
import Database.DSH
import Database.DSH.Flattening
import Database.X100Client

import Records

threadPosts :: Q [(Thread, Post)]
threadPosts =
        [ tuple (thread, post)
        | thread <- threads
        , post   <- posts
        , (spiegel_thread_urlQ thread == spiegel_post_thread_urlQ post)  
	  && (spiegel_thread_hitsQ thread) > (toQ (2000 :: Integer)) ]

getConn :: IO X100Info
getConn = P.return $ x100Info "localhost" "48130" Nothing

main :: IO ()
main = getConn 
       P.>>= (\conn -> debugX100VL conn threadPosts)
       P.>>= (\res -> putStrLn $ P.show res)
