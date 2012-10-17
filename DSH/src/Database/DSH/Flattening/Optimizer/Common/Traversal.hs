-- | This module provides wrappers around the traversal functions from
-- TableAlgebra. It extracts the shape (and potentially other
-- additional information provided in OptRewrite) and runs an OptMatch
-- instead of a DefaultMatch with it.

module Optimizer.Common.Traversal where

import Database.Algebra.Dag
import Database.Algebra.Dag.Common
import Database.Algebra.Rewrite
import qualified Database.Algebra.Rewrite.Traversal as R

import Optimizer.Common.Match
import Optimizer.Common.Rewrite

preOrder :: (Operator o)
            => OptRewrite o (NodeMap p)
            -> RuleSet OptMatch OptRewrite o p
            -> OptRewrite o Bool
preOrder inferAction rules = do
  sh <- shape
  R.preOrder (runOptMatch sh) inferAction rules
  
postOrder :: (Operator o)
             => OptRewrite o (NodeMap p)
             -> RuleSet OptMatch OptRewrite o p
             -> OptRewrite o Bool
postOrder inferAction rules = do
  sh <- shape
  R.postOrder (runOptMatch sh) inferAction rules
  
topologically :: (Operator o)
                 => OptRewrite o (NodeMap p)
                 -> RuleSet OptMatch OptRewrite o p
                 -> OptRewrite o Bool
topologically inferAction rules = do
  sh <- shape
  R.preOrder (runOptMatch sh) inferAction rules
        
iteratively :: DagRewrite (r o) o => r o Bool -> r o Bool
iteratively = R.iteratively

sequenceRewrites :: DagRewrite (r o) o => [r o Bool] -> r o Bool
sequenceRewrites = R.sequenceRewrites
