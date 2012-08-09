{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Optimizer.Common.Match where

import Data.Functor

import Control.Applicative
import Control.Monad.Trans
import Control.Monad.Trans.Reader

import Database.Algebra.Dag(AlgebraDag, Operator)
import Database.Algebra.Dag.Common
import qualified Database.Algebra.Rewrite as RM
  
import Optimizer.Common.Shape

-- | The Match monad models the failing of a match and provides limited read-only access
-- to the DAG and the shape of the result.
newtype OptMatch o p a = M (ReaderT Shape (RM.Match o p) a) deriving (Monad, Functor, Applicative)

getShape :: OptMatch o p Shape
getShape = M $ ask

-- | Runs a match on the supplied DAG. If the Match fails, 'Nothing' is returned.
-- If the Match succeeds, it returns just the result.
runMatch :: AlgebraDag o -> NodeMap p -> Shape -> OptMatch o p a -> Maybe a
runMatch d pm sh (M match) = RM.runMatch d pm (runReaderT match sh)
                             
-- | Returns the parents of a node in a OptMatch context.
getParents :: AlgNode -> OptMatch o p [AlgNode]
getParents q = M $ lift $ RM.getParents q

getOperator :: AlgNode -> OptMatch o p o
getOperator q = M $ lift $ RM.getOperator q

hasPath :: AlgNode -> AlgNode -> OptMatch o p Bool
hasPath q1 q2 = M $ lift $ RM.hasPath q1 q2
                
getRootNodes :: OptMatch o p [AlgNode]
getRootNodes = M $ lift RM.getRootNodes

-- | Fails the complete match if the predicate is False.
predicate :: Bool -> OptMatch o p ()
predicate True    = M $ return ()
predicate False   = M $ fail ""
               
-- | Fails the complete match if the value is Nothing
try :: Maybe a -> OptMatch o p a
try (Just x) = return x
try Nothing  = fail ""
                    
-- | Runs the supplied OptMatch action on the operator that belongs to the given node.
matchOp :: Operator o => AlgNode -> (o -> OptMatch o p a) -> OptMatch o p a
matchOp q match = getOperator q >>= (\op -> match op)

-- | Look up the properties for a given node.
properties :: AlgNode -> OptMatch o p p
properties q = M $ lift $ RM.properties q
