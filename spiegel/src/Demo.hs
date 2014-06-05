{-# LANGUAGE QuasiQuotes, OverloadedStrings #-}

module Main where

import Prelude()
import Database.DSH

import Records

postQuotes :: Q [(Post,[Quote])]
postQuotes =
  [$qc| tuple (the post, quote)
      | post  <- posts
      , quote <- quotes
      , spiegel_post_urlQ post == spiegel_quote_urlQ quote
      , then group by (spiegel_post_urlQ post)
  |]









numberOfQuotesReceivedByEachAuthor :: Q [(Text,Integer)]
numberOfQuotesReceivedByEachAuthor =
  [$qc| tuple (the postAuthor, sum quoteNumber)
      | (post,quotes) <- postQuotes
      , let quoteNumber = length quotes
      , let postAuthor  = spiegel_post_user_urlQ post
      , then group by postAuthor
  |]








main :: IO ()
main = do
  debugQ numberOfQuotesReceivedByEachAuthor
    >>= putStrLn
  runQ numberOfQuotesReceivedByEachAuthor
    >>= csvExport "numberOfQuotesReceivedByEachAuthor.csv"