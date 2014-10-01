{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MonadComprehensions   #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE RebindableSyntax      #-}
{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE UndecidableInstances  #-}
{-# LANGUAGE ViewPatterns          #-}

module Main where


import qualified Prelude as P
import Database.DSH
import Database.DSH.Compiler

import Database.X100Client

import Database.HDBC.PostgreSQL

import TPCH

getConn :: IO Connection
getConn = connectPostgreSQL "user = 'au' password = 'foobar' host = 'localhost' port = '5432' dbname = 'tpch'"

x100Conn :: X100Info
x100Conn = undefined

foo :: Q [(Integer, Integer, Integer)]
foo = [ triple a c 42 | (view -> (a, b, c)) <- toQ ([(1,2,3), (4,5,6), (7,8,9)] :: [(Integer, Integer, Integer)]) ]

main :: IO ()
-- main = getConn P.>>= \c -> debugQ "q" c $ qj3 $ toQ (([], [], []) :: ([Integer], [Integer], [Integer]))
-- main = getConn P.>>= \c -> debugQ "q" c foo
main = getConn P.>>= \c -> runQ c foo P.>>= \r -> putStrLn $ show r
--main = debugQX100 "q" x100Conn $ q (toQ [1..50])
--main = debugQX100 "q1" x100Conn q1
