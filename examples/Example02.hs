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

dept :: Q (Text, Text, Integer) -> Q Text
dept (view -> (_, d, _)) = d

sal :: Q (Text, Text, Integer) -> Q Integer
sal (view -> (_, _, s)) = s

name :: Q (Text, Text, Integer) -> Q Text
name (view -> (n, _, _)) = n

-- The duplicate-free list of departments.
departments :: Q [Text]
departments = nub [ dept e | e <- employees]

-- The total salary for a given department
deptSalary :: Q Text -> Q Double
deptSalary d = avg [ sal e | e <- employees , d == dept e ]

-- For each department, compute the total salary.
deptSalaries :: Q [(Text, Double)]
deptSalaries = [ pair d (deptSalary d)
               | d <- departments
               ]

-- Alternatively, employ the 'groupWithKey' combinator to express
-- grouping.
deptSalaries' :: Q [(Text, Double)]
deptSalaries' = [ pair d (avg [ sal ge | ge <- g ])
                | (view -> (d, g)) <- groupWithKey dept employees
                ]

-- Query with a nested result: For each department, compute the list
-- of employees.
employeesPerDept :: Q [(Text, [Text])]
employeesPerDept = [ pair d [ name e | e <- employees, dept e == d ]
                   | d <- departments
                   ]

getConn :: IO Connection
getConn = connectPostgreSQL "user = 'au' password = 'foobar' host = 'localhost' dbname = 'test'"

execQ :: (Show a,QA a) => Q a -> IO ()
execQ q = getConn P.>>= \conn -> (runQ conn q P.>>= P.print) P.>> disconnect conn

main :: IO ()
main = execQ deptSalaries
       P.>> execQ deptSalaries'
       P.>> execQ employeesPerDept
