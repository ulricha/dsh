{-# LANGUAGE TemplateHaskell       #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE MultiParamTypeClasses #-}

{-# OPTIONS_GHC -Wall -O3 -fno-warn-orphans -fno-warn-overlapping-patterns #-}
module Main where
       
import           ComprehensionTests
import           CombinatorTests

#ifdef TESTX100
import           Database.X100Client
#elif TESTSQL
import           Database.HDBC.PostgreSQL
#endif

import           System.Environment
import           Test.Framework (Test, defaultMainWithArgs)
import           Test.QuickCheck

import           Data.List


#ifdef TESTX100
getConn :: IO X100Info
getConn = return $ x100Info "localhost" "48130" Nothing
#elif TESTSQL
getConn :: IO Connection
getConn = connectPostgreSQL "user = 'au' password = 'foobar' host = 'localhost' dbname = 'test'"
#endif

qc :: Testable prop => prop -> IO ()
qc = quickCheckWith stdArgs{maxSuccess = 100, maxSize = 5}

putStrPad :: String -> IO ()
putStrPad s = putStr (s ++ replicate (32 - length s) ' ' )


main :: IO ()
main = do
            args <- getArgs
            let args' = if or $ map (isPrefixOf "-s") args
                         then args
                         else "-s5":args
            defaultMainWithArgs tests args'

tests :: [Test]
tests =
    [ tests_types
    , tests_tuples
    , tests_join_hunit
    , tests_nest_head_hunit
    , tests_nest_guard_hunit
    , tests_combinators_hunit
    , tests_comprehensions
    , tests_boolean
    , tests_numerics
    , tests_maybe
    , tests_either
    , tests_lists
    , tests_lifted
    ]
