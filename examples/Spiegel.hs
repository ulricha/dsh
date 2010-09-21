{-# LANGUAGE TemplateHaskell, FlexibleInstances, MultiParamTypeClasses, QuasiQuotes, OverloadedStrings #-}

module Spiegel where

import Ferry
import Database.HDBC.PostgreSQL


getConnection :: IO Connection
getConnection = connectPostgreSQL "user = 'postgres' host = 'localhost' dbname = 'onlineForums'"


$(createTableRepresentation
      (connectPostgreSQL "user = 'postgres' host = 'localhost' dbname = 'onlineForums'")
      "spiegelUsers" "User" [''Show,''Eq])


$(createTableRepresentation
      (connectPostgreSQL "user = 'postgres' host = 'localhost' dbname = 'onlineForums'")
      "spiegelPosts" "Post" [''Show,''Eq])