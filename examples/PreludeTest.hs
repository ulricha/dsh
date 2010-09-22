module PreludeTest where

import qualified Ferry as Q
import qualified Ferry.HSCompiler as C
import qualified Ferry.Interpreter as I

import Database.HDBC (IConnection, disconnect)
import Database.HDBC.PostgreSQL

import Test.QuickCheck
import Test.QuickCheck.Monadic

getConn :: IO Connection
getConn = connectPostgreSQL "user = 'postgres' password = 'haskell98' host = 'localhost' dbname = 'ferry'"

main :: IO ()
main = do
    putStrLn "Running DSH prelude tests"
    putStrLn "-------------------------"
    quickCheck prop_fst
    quickCheck prop_snd
    quickCheck prop_and
    quickCheck prop_or
    quickCheck prop_not

runTest :: (Eq b, Q.QA a, Q.QA b) => (Q.Q a -> Q.Q b) -> (a -> b) -> a -> Property
runTest q f arg = monadicIO $ do
                          c <- run $ getConn
                          db <- run $ C.fromQ c $ q (Q.toQ arg) 
                          it <- run $ I.fromQ c $ q (Q.toQ arg)
                          run $ disconnect c
                          let hs = f arg
                          assert (db == hs && it == hs)

prop_fst :: (Integer, Integer) -> Property
prop_fst = runTest Q.fst fst

prop_snd :: (Integer, Integer) -> Property
prop_snd = runTest Q.snd snd

prop_and :: [Bool] -> Property
prop_and = runTest Q.and and

prop_or :: [Bool] -> Property
prop_or = runTest Q.or or

prop_not :: Bool -> Property
prop_not = runTest Q.not not
