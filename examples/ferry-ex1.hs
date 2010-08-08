{-# LANGUAGE TemplateHaskell, ScopedTypeVariables , FlexibleInstances,
  MultiParamTypeClasses, TypeSynonymInstances #-}

{-# OPTIONS -fno-warn-orphans #-}

import Database.HDBC.PostgreSQL

import Ferry hiding (map)

$(createTableRepresentation
    (connectPostgreSQL "user = 'postgres' host = 'localhost' dbname='ferry'")
    "users"     -- table name
    "User"      -- data name
    [''Show]
 )

main :: IO ()
main = do

    -- Get the PostgreSQL connection
    c <- connectPostgreSQL "user = 'postgres' host = 'localhost' dbname='ferry'"

    -- Just get the whole table content here to see if everything works correct:
    u  <- fromQ c (table "users" :: Q [(Int,String)])
    putStrLn $ "Table content as Tuple:\n\t" ++ show u ++ "\n"

    -- Now use our custom `User' data type:
    u' <- fromQ c (table "users" :: Q [User])
    putStrLn $ "Table content as `User':\n\t" ++ show u' ++ "\n"
