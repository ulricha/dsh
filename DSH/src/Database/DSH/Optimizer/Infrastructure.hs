{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Database.DSH.Optimizer.Rewrite where

import Control.Applicative
import Control.Monad.Trans.State
  
import Data.Functor

import Database.Algebra.Dag.Common
import Database.Algebra.Rewrite
import Database.Algebra.VL.Data

data DBV = DBV AlgNode [DBCol]

data DBP = DBP AlgNode [DBCol]
  
  
data Layout = InColumn Int
            | Nest DBV Layout
            | Pair Layout Layout
              
data Shape = ValueVector DBV Layout
           | PrimVal DBP Layout
             
newtype OptMatch o p a = O (StateT Shape (Match o p) a)
                       deriving (Monad, Functor, Applicative)
                                

                                
