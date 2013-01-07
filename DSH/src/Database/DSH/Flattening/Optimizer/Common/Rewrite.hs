module Database.DSH.Flattening.Optimizer.Common.Rewrite
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
  , R.updateExtras
  , R.insert
  , R.insertNoShare
  , R.replaceChild
  , R.infer
  , R.collect
  )

where

import qualified Database.Algebra.Dag                           as D
import           Database.Algebra.Dag.Common
import qualified Database.Algebra.Rewrite.DagRewrite            as R
import           Database.Algebra.Rewrite.Match
import           Database.Algebra.Rewrite.PatternConstruction   (pattern, v)
import           Database.Algebra.Rewrite.Properties
import           Database.Algebra.Rewrite.Rule
import           Database.Algebra.Rewrite.Traversal
import           Database.DSH.Flattening.Optimizer.Common.Shape

replaceRoot :: D.Operator o => AlgNode -> AlgNode -> R.Rewrite o Shape ()
replaceRoot oldRoot newRoot = do
  sh <- R.getExtras
  R.updateExtras $ updateShape oldRoot newRoot sh
  R.replaceRoot oldRoot newRoot

replaceWithNew :: (D.Operator o, Show o) => AlgNode -> o -> R.Rewrite o Shape AlgNode
replaceWithNew oldNode newOp = do
  sh <- R.getExtras
  newNode <- R.replaceWithNew oldNode newOp
  R.updateExtras $ updateShape oldNode newNode sh
  return newNode

replace :: D.Operator o => AlgNode -> AlgNode -> R.Rewrite o Shape ()
replace oldNode newNode = do
  sh <- R.getExtras
  R.replace oldNode newNode
  R.updateExtras $ updateShape oldNode newNode sh
