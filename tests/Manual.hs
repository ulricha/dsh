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

-- import qualified Data.Text as T

import TPCH

data Foo = Foo { foo1 :: Integer, foo2 :: Text, foo3 :: Integer }

deriveDSH ''Foo
deriveTA ''Foo
generateTableSelectors ''Foo

getConn :: IO Connection
getConn = connectPostgreSQL "user = 'au' password = 'foobar' host = 'localhost' port = '5432' dbname = 'tpch'"

x100Conn :: X100Info
x100Conn = x100Info "localhost" "48130" Nothing

xs :: Q [(Text, [Integer])]
xs = toQ [("a", [10, 20]), ("b", [30, 40])]

q :: Q [[Integer]]
q = map snd xs

main :: IO ()
main = getConn P.>>= \c -> debugQ "q" c q  P.>>= \r -> putStrLn (show r)
-- main = runQX100 x100Conn q P.>>= \r -> putStrLn $ show r
--main = debugQX100 "q" x100Conn q
