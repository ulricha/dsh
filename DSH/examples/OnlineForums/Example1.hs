{-# LANGUAGE QuasiQuotes, OverloadedStrings #-}

module Main where

-- import qualified Prelude as P
-- 
-- import Database.DSH 
-- import Database.DSH.Interpreter
-- 
-- import Spiegel
-- 
-- 
-- users :: Q [User]
-- users = table "spiegelUsers"
-- 
-- posts :: Q [Post]
-- posts = table "spiegelPosts"
-- 
-- isBetweenDates :: Q Post -> (Q Time,Q Time) -> Q Bool
-- isBetweenDates p (d1,d2) = (spiegelPostTimeQ p >= d1) && (spiegelPostTimeQ p <= d2)
-- 
-- isAuthorOf :: Q User -> Q Post -> Q Bool
-- isAuthorOf u p = spiegelPostAuthorUserNameQ p == spiegelUserNameQ u
-- 
-- postsBetweenDates :: Q User -> Q Time -> Q Time -> Q [Post] -> Q [Post]
-- postsBetweenDates u d1 d2 ps = [$qc|
--      p | p <- ps , u `isAuthorOf` p , p `isBetweenDates` (d1,d2)
--   |]
-- 
-- numberOfPostsBetweenDates :: Q User -> Q Time -> Q Time -> Q [Post] -> Q Integer
-- numberOfPostsBetweenDates u d1 d2 ps = length (postsBetweenDates u d1 d2 ps)
-- 
-- date1 :: Q Time
-- date1 = toQ (P.read "2005-01-01 00:00:00 UTC")
-- 
-- date2 :: Q Time
-- date2 = toQ (P.read "2010-01-01 00:00:00 UTC")
-- 
-- umberto :: Q User
-- umberto = the [$qc| u | u <- users, spiegelUserNameQ u == "Umberto" |]

main :: IO ()
main = do
  -- conn <- getConnection
  -- 
  -- u <- fromQ conn umberto
  -- P.print u
  -- 
  -- n <- fromQ conn (numberOfPostsBetweenDates (toQ u) date1 date2 posts)
  -- P.print n
  return ()