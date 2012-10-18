{-# LANGUAGE MonadComprehensions #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RebindableSyntax    #-}
{-# LANGUAGE ViewPatterns        #-}

module Main where

import qualified Prelude as P
import Database.DSH
import Database.DSH.Compiler

import Database.HDBC.PostgreSQL

employees :: Q [(Text, Text, Integer)]
employees = toQ [ ("Simon",  "MS",   80)
							  , ("Erik",   "MS",   90)
							  , ("Phil",   "Ed",   40)
							  , ("Gordon", "Ed",   45)
							  , ("Paul",   "Yale", 60)
							  ]

departments :: Q [Text]
departments = nub [ dept | (view -> (_name,dept,_salary)) <- employees]

deptSalary :: Q Text -> Q Integer
deptSalary dept = sum [ salary
                      | (view -> (_name,dept',salary)) <- employees
                      , dept == dept']

mainQuery :: Q [(Text,Integer)]
mainQuery = [ pair dept (deptSalary dept)
            | dept <- departments]

getConn :: IO Connection
getConn = connectPostgreSQL "user = 'giorgidz' password = '' host = 'localhost' dbname = 'giorgidz'"

runQ :: (Show a,QA a) => Q a -> IO ()
runQ q = getConn P.>>= \conn -> (fromQ conn q P.>>= P.print) P.>> disconnect conn

main :: IO ()
main = runQ mainQuery