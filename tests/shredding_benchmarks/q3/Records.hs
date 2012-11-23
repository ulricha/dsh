{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}

module Records where

import Control.Exception

import Database.DSH
import Database.DSH.Compiler

import Database.X100Client

{-
data User = User
    { spiegel_user_url           :: Text
    , spiegel_user_name          :: Text
    , spiegel_user_role          :: Text
    , spiegel_user_posts         :: Integer
    , spiegel_user_posts_per_day :: Double
    , spiegel_user_registered    :: Double
    , spiegel_user_last_activity :: Double
    }
    
data Thread = Thread
    { spiegel_thread_url         :: Text
    , spiegel_thread_title       :: Text
    , spiegel_thread_description :: Text
    , spiegel_thread_replies     :: Integer
    , spiegel_thread_hits        :: Integer
    , spiegel_thread_rating      :: Double
    , spiegel_thread_votes       :: Integer
    }
    
data Post = Post
    { spiegel_post_url        :: Text
    , spiegel_post_thread_url :: Text
    , spiegel_post_time       :: Double
    , spiegel_post_subject    :: Text
    , spiegel_post_content    :: Text
    , spiegel_post_user_name  :: Text
    , spiegel_post_user_url   :: Text
    }

deriveDSH ''User
deriveDSH ''Thread
deriveDSH ''Post

users :: Q [User]
-- users = tableWithKeys "spiegel_users" [["spiegel_user_url"]]
users = toQ []

threads :: Q [Thread]
-- threads = tableWithKeys "spiegel_threads" [["spiegel_thread_url"]]
threads = toQ []

posts :: Q [Post]
-- posts = tableWithKeys "spiegel_posts" [["spiegel_post_url"]]
posts = toQ []
-}

type User = (Text, Text)

users :: Q [User]
users = toQ [ ("u1", "u1_name")
            , ("u2", "u2_name")
	    ]

type Thread = (Text, Text)

threads :: Q [Thread]
threads = toQ [ ("t1", "t1_title")
              , ("t2", "t2_title")
	      ]

type Post = (Text, Text, Text)

posts :: Q [Post]
posts = toQ [ ("p1", "t1", "u1")
            , ("p2", "t1", "u2")
	    , ("p3", "t2", "u2")
	    ]
