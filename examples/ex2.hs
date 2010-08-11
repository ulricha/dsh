{-# LANGUAGE TemplateHaskell, ScopedTypeVariables , FlexibleInstances,
  MultiParamTypeClasses, TypeSynonymInstances #-}

{-# OPTIONS -fno-warn-orphans #-}


import Database.HDBC.PostgreSQL
import System.Exit


import Ferry hiding (map)
import qualified Ferry as Q


--------------------------------------------------------------------------------
-- Our table
--

$(createTableRepresentation
    (connectPostgreSQL "user = 'postgres' host = 'localhost' dbname = 'ferry'")
    "users"                     -- table name
    "User"                      -- data name
    [''Show]                    -- deriving
 )

userTable :: Q [User]
userTable = table "users"


--------------------------------------------------------------------------------
-- A few simple Ferry expressions
--

firstUserName :: Q String
firstUserName = q'user_name $ Q.head userTable

allIds :: Q [Int]
allIds = Q.map q'user_id userTable

allNames :: Q [String]
allNames = Q.map q'user_name userTable

numberOfUsers :: Q Int
numberOfUsers = Q.length userTable

emptyDatabase :: Q Bool
emptyDatabase = Q.null userTable


--------------------------------------------------------------------------------
-- IO functions
--

main :: IO ()
main = do

    -- Get the PostgreSQL connection
    c <- connectPostgreSQL "user = 'postgres' host = 'localhost' dbname='ferry'"

    -- Get the whole table content
    u <- fromQ c userTable
    putStrLn "Table content:"
    mapM_ (\user -> putStrLn $ "\t· " ++ show user) u
    putStrLn ""

    -- Let's test our Ferry expressions:

    empty <- fromQ c emptyDatabase
    if empty
       then do putStrLn "Database is empty! :("
               exitFailure
       else putStrLn "Database is not empty! :)"

    first <- fromQ c firstUserName
    putStrLn $ "First username is: " ++ show first

    ids <- fromQ c allIds
    putStrLn $ "All IDs in database: " ++ show ids

    names <- fromQ c allNames
    putStrLn $ "All names in database: " ++ show names

    total <- fromQ c numberOfUsers
    putStrLn $ "Total number of users in database: " ++ show total
