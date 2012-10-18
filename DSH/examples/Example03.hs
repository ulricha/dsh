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

import Database.HDBC.PostgreSQL

data Employee = Prof  { name            :: Text
                      , chair           :: Text
                      , advisedStudents :: [Text]
                      }
              | Stud  { name    :: Text
                      , topic   :: Text
                      , advisor :: Text
                      }
              deriving (Eq,Ord,Show)

deriveDSH ''Employee

students :: Q [(Integer,Text,Text,Text)]
students = toQ  [ (1,"J","P","T")
                , (2,"A","Q","T")
                ]

professors :: Q [(Integer,Text,Text)]
professors = toQ  [ (0,"T","DB")]

employment :: Q [(Integer,Text,Text,Integer)]
employment = toQ  [ (0,"DB","professor",2008)
                  , (1,"DB","student",2010)
                  , (2,"DB","student",2011)
                  , (3,"PL","student",2012)
                  ]

salaries :: Q [(Integer,Integer)]
salaries = toQ  [ (0,4096)
                , (1,2048)
                , (2,2048)
                ]

employeesBySeniority :: Q [Employee]
employeesBySeniority = concat
  [ if eStatus == "student"
       then  [ stud sName sTopic sAdvisor
             | (view -> (sID, sName, sTopic, sAdvisor)) <- students
             , eID == sID
             ]
       else  [  prof pName pChair sAdvised
             |  (view -> (pID, pName, pChair)) <- professors
             ,  eID == pID
             ,  let sAdvised = [ sName
                               | (view -> (_, sName, _, sAdvisor)) <- students
                               , sAdvisor == pName
                               ]
             ]
  | (view -> (eID, _, eStatus, _)) <- sortWith (\(view -> (_, _, _, d)) -> d) employment
  ]

safeMinimum :: (Ord a, QA a) => Q [a] -> Q (Maybe a)
safeMinimum as = if null as then nothing else just (minimum as) 

salPerDept :: Q [(Text, [Integer])]
salPerDept =
  [ pair dept [ salary
              | (view -> (sID,salary)) <- salaries
              , (view -> (dID,_,_,_)) <- deptMembers
              , sID == dID
              ]
  | (view -> (dept, deptMembers)) <- groupWithKey (\(view -> (_,d,_,_)) -> d) employment
  ]

minSalPerDept :: Q [(Text, Integer)]
minSalPerDept =  [ pair dept (elim (safeMinimum sals)
                                   0
                                   (\minSal -> minSal))
                 | (view -> (dept, sals)) <- salPerDept
                 ]

getConn :: IO Connection
getConn = connectPostgreSQL "user = 'giorgidz' password = '' host = 'localhost' dbname = 'giorgidz'"

runQ :: (Show a,QA a) => Q a -> IO ()
runQ q = getConn P.>>= \conn -> (fromQ conn q P.>>= P.print) P.>> disconnect conn

main :: IO ()
main = sequence_  [ runQ employeesBySeniority
                  , runQ salPerDept
                  , runQ minSalPerDept
                  ]