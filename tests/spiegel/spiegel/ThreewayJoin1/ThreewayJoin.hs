-- 536fe6f6729670107a8ba7e66f510d017bbe118b
-- optimization string: ERSRS

{-# LANGUAGE OverloadedStrings, MonadComprehensions, RebindableSyntax, ViewPatterns #-}

module Main where

import qualified Prelude as P
import Database.DSH
import Database.DSH.Flattening
import Database.X100Client

import Records

-- Helper Functions and Queries
  
threewayJoin :: Q [(Text, Text)]
threewayJoin =
        [ pair uName tTitle
        | (view -> (tUrl, tTitle))               <- threads
        , (view -> (pUrl, pThreadUrl, pUserUrl)) <- posts
	, (view -> (uUrl, uName))                <- users
        , tUrl == pThreadUrl
	  && uUrl == pUserUrl ]

getConn :: IO X100Info
getConn = P.return $ x100Info "localhost" "48130" Nothing

main :: IO ()
main = getConn 
       P.>>= (\conn -> debugX100VL conn threewayJoin)
       P.>>= (\res -> putStrLn $ P.show res)
