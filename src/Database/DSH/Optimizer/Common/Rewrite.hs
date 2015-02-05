module Database.DSH.Common.Opt
  ( module Database.Algebra.Rewrite.Match
  , module Database.Algebra.Rewrite.PatternConstruction
  , module Database.Algebra.Rewrite.Properties
  , module Database.Algebra.Rewrite.Rule
  , module Database.Algebra.Rewrite.Traversal
  , replaceRoot
  , replaceWithNew
  , replace
  , R.Rewrite
  , R.runRewrite
  , R.initRewriteState
  , R.Log
  , R.logGeneral
  , R.logRewrite
  , R.parents
  , R.topsort
  , R.operator
  , R.rootNodes
  , R.exposeDag
  , R.getExtras
  , R.condRewrite
  , R.updateExtras
  , R.insert
  , R.insertNoShare
  , R.replaceChild
  , R.infer
  , R.collect
  )

where

import qualified Database.Algebra.Dag                          as D
import           Database.Algebra.Dag.Common
import qualified Database.Algebra.Rewrite.DagRewrite           as R
import           Database.Algebra.Rewrite.Match
import           Database.Algebra.Rewrite.PatternConstruction  (dagPatMatch, v)
import           Database.Algebra.Rewrite.Properties
import           Database.Algebra.Rewrite.Rule
import           Database.Algebra.Rewrite.Traversal

import           Database.DSH.Common.QueryPlan
import           Database.DSH.VL.Vector

--------------------------------------------------------------
-- Versions of rewrite combinators that maintain the Shape
-- description of the query structure.

-- | Replace a root node while maintaining the query structure
-- information.
replaceRoot :: (DagVector v, D.Operator o) => AlgNode -> AlgNode -> R.Rewrite o (Shape v) ()
replaceRoot oldRoot newRoot = do
  sh <- R.getExtras
  R.updateExtras $ updateShape oldRoot newRoot sh
  R.replaceRoot oldRoot newRoot

-- | Replace a node with a new operator while mainting the query
-- structure information.
replaceWithNew :: (D.Operator o, Show o, DagVector v) 
               => AlgNode -> o -> R.Rewrite o (Shape v) AlgNode
replaceWithNew oldNode newOp = do
  sh <- R.getExtras
  newNode <- R.replaceWithNew oldNode newOp
  R.updateExtras $ updateShape oldNode newNode sh
  return newNode

-- | Replace a node with another node while maintaining the query
-- structure information.
replace :: (DagVector v, D.Operator o) 
        => AlgNode -> AlgNode -> R.Rewrite o (Shape v) ()
replace oldNode newNode = do
  sh <- R.getExtras
  R.replace oldNode newNode
  R.updateExtras $ updateShape oldNode newNode sh
