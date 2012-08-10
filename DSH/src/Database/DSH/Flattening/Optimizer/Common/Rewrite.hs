{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleInstances, MultiParamTypeClasses #-}

module Optimizer.Common.Rewrite where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Trans.State
  
import Database.Algebra.Dag
import qualified Database.Algebra.Rewrite as DR
  
import Optimizer.Common.Shape

-- | An extended version of the DefaultRewrite rewrite monad which
-- provides access to the shape of a query. 
newtype OptRewrite o r = O (StateT Shape (DR.DefaultRewrite o) r) deriving (Monad, Functor, Applicative)
                      
runOptRewrite :: Operator o => OptRewrite o r -> Shape -> AlgebraDag o -> (AlgebraDag o, Shape, DR.Log)
runOptRewrite (O rewrite) sh dag = (dag', sh', rewriteLog)
  where (dag', (_, sh'), rewriteLog) = DR.runDefaultRewrite (runStateT rewrite sh) dag 

-- | Return the shape description of the query
shape :: OptRewrite o Shape
shape = O get
        
instance DR.DagRewrite (OptRewrite o) o where
  getDag = O $ lift $ DR.getDag
        
  logGeneral m = O $ lift $ DR.logGeneral m
               
  logRewrite m n = O $ lift $ DR.logRewrite m n

  reachableNodesFrom n = O $ lift $ DR.reachableNodesFrom n
                       
  infer f = O $ lift $ DR.infer f
                       
  parents n = O $ lift $ DR.parents n

  topsort = O $ lift DR.topsort
          
  operator n = O $ lift $ DR.operator n

  rootNodes = O $ liftM rootsFromShape get

  insert op = O $ lift $ DR.insert op

  replaceChild n old new = O $ lift $ DR.replaceChild n old new

  relinkParents old new = O $ lift $ DR.relinkParents old new

  relinkToNew oldNode newOp = O $ lift $ DR.relinkToNew oldNode newOp

  replace node newOp = O $ lift $ DR.replace node newOp

  pruneUnused = O $ lift DR.pruneUnused
  
  replaceRoot oldRoot newRoot = O $ do
    s <- get
    put $ updateShape oldRoot newRoot s
    lift $ DR.replaceRoot oldRoot newRoot

