{-# LANGUAGE GeneralizedNewtypeDeriving, FlexibleInstances, MultiParamTypeClasses #-}

module Optimizer.Common.Match where

import Control.Applicative
import Control.Monad.Trans
import Control.Monad.Trans.Reader

import Database.Algebra.Dag(AlgebraDag)
import Database.Algebra.Dag.Common
import qualified Database.Algebra.Rewrite.Match as RM
import Database.Algebra.Rewrite()
  
import Optimizer.Common.Shape

-- | The Match monad models the failing of a match and provides limited read-only access
-- to the DAG and the shape of the result.
newtype OptMatch o p a = M (ReaderT Shape (RM.DefaultMatch o p) a) deriving (Monad, Functor, Applicative)

getShape :: OptMatch o p Shape
getShape = M $ ask

runOptMatch :: Shape -> AlgebraDag o -> NodeMap p -> OptMatch o p a -> Maybe a
runOptMatch sh d pm (M match) = RM.runDefaultMatch d pm (runReaderT match sh)

properties :: AlgNode -> OptMatch o p p
properties q = M $ lift $ RM.properties q

matchOp :: AlgNode -> (o -> OptMatch o p a) -> OptMatch o p a
-- matchOp q match = M $ (lift (RM.getOperator q)) >>= (\op -> match op)
matchOp q match = M $ do
  op <- lift (RM.getOperator q)
  let M m = match op
  m

try :: Maybe a -> OptMatch o p a
try (Just x) = return x
try Nothing  = fail ""

predicate :: Bool -> OptMatch o p ()
predicate True    = M $ return ()
predicate False   = M $ fail ""

getRootNodes :: OptMatch o p [AlgNode]
getRootNodes = M $ lift RM.getRootNodes

hasPath :: AlgNode -> AlgNode -> OptMatch o p Bool
hasPath q1 q2 = M $ lift $ RM.hasPath q1 q2

getOperator :: AlgNode -> OptMatch o p o
getOperator q = M $ lift $ RM.getOperator q

getParents :: AlgNode -> OptMatch o p [AlgNode]
getParents q = M $ lift $ RM.getParents q
