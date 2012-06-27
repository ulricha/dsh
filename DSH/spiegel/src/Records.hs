{-# LANGUAGE TemplateHaskell, FlexibleInstances, MultiParamTypeClasses, CPP #-}

module Records where

import Control.Exception

import Database.DSH
import Database.DSH.Compiler

import Database.HDBC.PostgreSQL

#define getConnectionDef (connectPostgreSQL "user = 'postgres' password='haskell98' host = 'localhost' dbname = 'onlineForums'")

getConnection :: IO Connection
getConnection = getConnectionDef

$(generateTableRecordInstances getConnectionDef "spiegel_users"   "User"   [''Show,''Eq,''Ord])
$(generateTableRecordInstances getConnectionDef "spiegel_threads" "Thread" [''Show,''Eq,''Ord])
$(generateTableRecordInstances getConnectionDef "spiegel_posts"   "Post"   [''Show,''Eq,''Ord])
$(generateTableRecordInstances getConnectionDef "spiegel_quotes"  "Quote"  [''Show,''Eq,''Ord])

users :: Q [User]
users = tableWithKeys "spiegel_users" [["spiegel_user_url"]]

threads :: Q [Thread]
threads = tableWithKeys "spiegel_threads" [["spiegel_thread_url"]]

posts :: Q [Post]
posts = tableWithKeys "spiegel_posts" [["spiegel_post_url"]]

quotes :: Q [Quote]
quotes = table "spiegel_quotes"


runQ :: (QA a) => Q a -> IO a
runQ q =
  bracket getConnection
          disconnect
          (\conn -> fromQ conn q)

debugQ :: (QA a) => Q a -> IO String
debugQ q =
  bracket getConnection
          disconnect
          (\conn -> debugSQL conn q)